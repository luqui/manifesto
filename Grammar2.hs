{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grammar2 where

import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Rank2 (Product(..), Only(..))


-- Here Const, Only, and Product shapes are emulating their Rank2 combinators,
-- but they are "virtual", in that they are simplified away by the ($) type
-- family before we ever see their constructors.  (I have hidden the
-- constructors just to make sure!) It means we have to pass a little more
-- explicit type information around, but it also means that we can omit those
-- nuissance constructors everywhere, and, more importantly, that semantics
-- functors need not be representational, which means that you can, for
-- example, use a GADT to have declare different value types corresponding to
-- different types of nodes in the AST.  For example, expressions get a Value
-- as their semantics, but definitions get a (Name,Value) pair.
type (:*:) = Product

type family (h :: (* -> *) -> *) $ (f :: * -> *) :: * where
    Const t $ f = t
    Only t $ f = f t
    (h :*: h') $ f = (h $ f, h' $ f)
    h $ f = h f

class Shape h where
    toShapeConstr :: h $ f -> h f
    default toShapeConstr :: (h $ f) ~ h f => h $ f -> h f
    toShapeConstr = id
    fromShapeConstr :: h f -> h $ f
    default fromShapeConstr :: (h $ f) ~ h f => h f -> h $ f
    fromShapeConstr = id

instance Shape (Const a) where
    toShapeConstr = Const
    fromShapeConstr = getConst

instance Shape (Only a) where
    toShapeConstr = Only
    fromShapeConstr = fromOnly

instance (Shape h, Shape h') => Shape (Product h h') where
    toShapeConstr (x,y) = Pair (toShapeConstr x) (toShapeConstr y)
    fromShapeConstr (Pair x y) = (fromShapeConstr x, fromShapeConstr y)


-- A shape prism.  No funny business on the f, we use enough structural
-- isomorphisms that you could mess everything up that way.

data Proxy p = Proxy

data HPrism h' h = HPrism { 
    review  :: forall f. Proxy f -> (h $ f) -> (h' $ f),
    preview :: forall f. Proxy f -> (h' $ f) -> Maybe (h $ f)
  }

infixr 4 ≪?≫
infixr 5 ≪*≫, ≪*, *≫
infixr 3 ≪|≫
-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    (≪?≫) :: HPrism h' h -> g h -> g h'
    unit  :: g (Const ())
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    empty :: g h
    (≪|≫) :: g h -> g h -> g h

(*≫) :: (Grammar g) => g (Const ()) -> g h -> g h
s *≫ g = leftUnit ≪?≫ (s ≪*≫ g)
    where
    leftUnit :: HPrism h (Const () :*: h)
    leftUnit = HPrism (\_ (() , x) -> x) (\_ x -> Just (() , x))

(≪*) :: (Grammar g) => g h -> g (Const ()) -> g h
g ≪* s = rightUnit ≪?≫ (g ≪*≫ s)
    where
    rightUnit :: HPrism h (h :*: Const ())
    rightUnit = HPrism (\_ (x , ()) -> x) (\_ x -> Just (x , ()))

choice :: (Grammar g) => [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Const Char)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h $ Identity))

{-
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }
newtype GParser h = GParser { runGParser :: Parser (h Parser) }

instance Grammar Parser where
instance Locus h Parser
-}

newtype StringPrinter h = StringPrinter { runStringPrinter :: (h $ Identity) -> First String }

instance Grammar StringPrinter where
    p ≪?≫ pp = StringPrinter (runStringPrinter pp <=< First . preview p (Proxy :: Proxy Identity))
    unit = StringPrinter (\() -> pure "")
    pp ≪*≫ pp' = StringPrinter (\(h , h') -> liftA2 (<>) (runStringPrinter pp h) (runStringPrinter pp' h'))
    empty = StringPrinter (\_ -> mempty)
    pp ≪|≫ pp' = StringPrinter (\h -> runStringPrinter pp h <> runStringPrinter pp' h)

instance Syntax StringPrinter where
    symbol s = StringPrinter (\() -> pure s)
    char = StringPrinter (\c -> pure [c])

instance Locus h StringPrinter where
    locus pp = StringPrinter (\(Identity h) -> runStringPrinter pp h)


class Semantics f h where
    sem :: Proxy h -> h $ f -> f (h $ Identity)

newtype Annotate f h = Annotate { runAnnotate :: h $ Identity -> First (h $ f) }

instance Grammar (Annotate f) where
    p ≪?≫ ann = Annotate (fmap (review p (Proxy :: Proxy f)) . runAnnotate ann <=< First . preview p (Proxy :: Proxy Identity))
    unit = Annotate (\() -> pure ())
    ann ≪*≫ ann' = Annotate (\(h , h') -> liftA2 (,) (runAnnotate ann h) (runAnnotate ann' h'))
    empty = Annotate (\_ -> mempty)
    ann ≪|≫ ann' = Annotate (\h -> runAnnotate ann h <> runAnnotate ann' h)
    -- This is almost exactly the same as StringPrinter above.  How can we automate this?
    -- Only Identity `Rank2.Arrow` Compose First (Only f)

instance Syntax (Annotate f) where
    symbol = const unit
    char = Annotate (\c -> pure c)

-- When we are annotating with f, we can only have loci on shapes that have
-- a defined semantics for f.
instance (Semantics f h) => Locus h (Annotate f) where
    locus (Annotate ann) = Annotate (\(Identity h) -> sem (Proxy :: Proxy h) <$> ann h)


-- The abstract syntax.  Note the pattern of recusion: f on top, Identity the
-- rest of the way down.
type Expr = ExprF Identity
data ExprF f
    = Cat (f Expr) (f Expr)
    | Lit (f Char)

instance Shape ExprF

-- These should be automatically generated.
_Cat :: HPrism ExprF (Only Expr :*: Only Expr)
_Cat = HPrism (\_ (a, b) -> Cat a b)
              (\_ -> \case Cat a b -> Just (a,b)
                           _ -> Nothing)

_Lit :: HPrism ExprF (Only Char)
_Lit = HPrism (\_ c -> Lit c)
              (\_ -> \case Lit c -> Just c
                           _ -> Nothing)

-- The grammar.
-- We collect the types that need to be given semantics into the synonym 'Loci'.
type Loci g = (Syntax g, Locus ExprF g, Locus (Const Char) g)

-- Concrete syntax.
expr :: (Loci g) => g (Only Expr)
expr = locus $ choice
    [ symbol "(" *≫ (_Cat ≪?≫ expr ≪*≫ symbol " ++ " *≫ expr) ≪* symbol ")"
    , _Lit ≪?≫ locus char
    ]

-- Evaluation semantics. (It's a shame that we need to coerce for promoteConst,
-- that's what's causing all this Representational junk.  If not, EvalSem could
-- even be a GADT showing how to evaluate each type of representable thing.
-- There must be a better way.)
--
-- We give a semantics to each type required by Loci.
data family EvalSem a
data instance EvalSem Char = EChar Char
    deriving Show
data instance EvalSem Expr = EStr String
    deriving Show


instance Semantics EvalSem (Const Char) where
    sem _ c = EChar c

instance Semantics EvalSem ExprF where
    sem _ (Cat (EStr x) (EStr y)) = EStr (x ++ y)
    sem _ (Lit (EChar x)) = EStr [x]
    

-- Example expression.
pattern I :: a -> Identity a
pattern I x = Identity x

exampleExpr :: Expr
exampleExpr = Cat (I (Cat (I (Lit (I 'a'))) (I (Lit (I 'b'))))) (I (Lit (I 'c')))


main :: IO ()
main = do
    -- Pretty print.
    print $ runStringPrinter expr (I exampleExpr)
    -- Evaluate.
    print (runAnnotate expr (I exampleExpr) :: First (EvalSem Expr))
