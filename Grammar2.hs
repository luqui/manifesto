{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grammar2 where

import Control.Applicative (liftA2)
import qualified Control.Applicative as A
import Control.Monad ((<=<))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Rank2 (Product(..), Only(..))
import qualified Rank2

import qualified IncrementalParser as IP


-- Here Const, Only, and Product shapes are emulating their Rank2 combinators,
-- but they are "virtual", in that they are simplified away by the ($) type
-- family before we ever see their constructors.  It means we have to pass a
-- little more explicit type information around (which can be a pain), but it
-- also means that we can omit those nuissance constructors everywhere, and,
-- more importantly, that semantics functors need not be representational,
-- which means that you can, for example, use a GADT to have declare different
-- value types corresponding to different types of nodes in the AST.  For
-- example, expressions get a Value as their "eval" semantics, but definitions
-- get a (Name,Value) pair.
type (:*:) = Product

class (Rank2.Functor h) => Shape (h :: (k -> *) -> *) where
    type h $ (f :: k -> *) :: *
    type h $ f = h f

    toShapeConstr :: h $ f -> h f
    default toShapeConstr :: (h $ f ~ h f) => h $ f -> h f
    toShapeConstr = id
    fromShapeConstr :: h f -> h $ f
    default fromShapeConstr :: (h $ f ~ h f) => h f -> h $ f
    fromShapeConstr = id

instance Rank2.Functor (Const a) where
    _ <$> Const x = Const x

instance Shape (Const a) where
    type Const a $ f = a
    toShapeConstr = Const
    fromShapeConstr = getConst

instance Shape (Only a) where
    type Only a $ f = f a
    toShapeConstr = Only
    fromShapeConstr = fromOnly

instance (Shape h, Shape h') => Shape (Product h h') where
    type Product h h' $ f = (h $ f, h' $ f)
    toShapeConstr (x,y) = Pair (toShapeConstr x) (toShapeConstr y)
    fromShapeConstr (Pair x y) = (fromShapeConstr x, fromShapeConstr y)

-- Literal is like Const but regular
newtype Literal a f = Literal a
    deriving (Show)

instance Rank2.Functor (Literal a) where
    _ <$> Literal a = Literal a

_Literal :: HPrism (Literal a) (Const a)
_Literal = HPrism (\_ -> Literal) (\_ (Literal x) -> Just x)

instance Shape (Literal a)

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


newtype GParser h = GParser { runGParser :: IP.Parser (h $ Const ()) }

instance Grammar GParser where
    p ≪?≫ gp = GParser . fmap (review p (Proxy @(Const ()))) $ runGParser gp
    unit = GParser (pure ())
    gp ≪*≫ gp' = GParser (liftA2 (,) (runGParser gp) (runGParser gp'))
    empty = GParser A.empty
    gp ≪|≫ gp' = GParser (runGParser gp A.<|> runGParser gp')

instance Syntax GParser where
    symbol s = GParser (IP.symbol s)
    char = GParser IP.char

instance Locus h GParser where
    locus gp = GParser (Const <$> IP.erase (runGParser gp))



newtype StringPrinter h = StringPrinter { runStringPrinter :: (h $ Identity) -> First String }

instance Grammar StringPrinter where
    p ≪?≫ pp = StringPrinter (runStringPrinter pp <=< First . preview p (Proxy @Identity))
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


data Annotated f a where
    Annotated :: (h $ Identity ~ h Identity) => f (h $ Identity) -> h (Annotated f) -> Annotated f (h $ Identity)

instance (Semantics f h, Shape h, h $ Identity ~ h Identity) => Semantics (Annotated f) h where
    sem pxy hann = Annotated (sem pxy (fromShapeConstr hf)) shape
        where
        shape :: h (Annotated f)
        shape = toShapeConstr hann
        hf :: h f
        hf = Rank2.fmap (\(Annotated fa _) -> fa) shape


-- The abstract syntax.  Note the pattern of recusion: f on top, Identity the
-- rest of the way down.
type Expr = ExprF Identity
data ExprF f
    = Cat (f Expr) (f Expr)
    | Lit (f (Literal Char Identity))

instance Rank2.Functor ExprF where
    f <$> Cat a b = Cat (f a) (f b)
    f <$> Lit c = Lit (f c)

deriving instance Show (ExprF Identity) 
deriving instance Show (ExprF (Const ())) 

instance Shape ExprF

-- These should be automatically generated.
_Cat :: HPrism ExprF (Only Expr :*: Only Expr)
_Cat = HPrism (\_ (a, b) -> Cat a b)
              (\_ -> \case Cat a b -> Just (a,b)
                           _ -> Nothing)

_Lit :: HPrism ExprF (Only (Literal Char Identity))
_Lit = HPrism (\_ c -> Lit c)
              (\_ -> \case Lit c -> Just c
                           _ -> Nothing)

-- The grammar.
-- We collect the types that need to be given semantics into the synonym 'Loci'.
type Loci g = (Syntax g, Locus ExprF g, Locus (Literal Char) g)

-- Concrete syntax.
expr1 :: (Loci g) => g ExprF
expr1 = choice
    [ symbol "cat(" *≫ (_Cat ≪?≫ expr ≪*≫ symbol "," *≫ expr) ≪* symbol ")"
    , symbol "'" *≫ (_Lit ≪?≫ locus (_Literal ≪?≫ char)) ≪* symbol "'"
    ]

expr :: (Loci g) => g (Only Expr)
expr = locus expr1

-- Evaluation semantics. (It's a shame that we need to coerce for promoteConst,
-- that's what's causing all this Representational junk.  If not, EvalSem could
-- even be a GADT showing how to evaluate each type of representable thing.
-- There must be a better way.)
--
-- We give a semantics to each type required by Loci.
data family EvalSem a
data instance EvalSem (Literal Char Identity) = EChar Char
    deriving Show
data instance EvalSem Expr = EStr String
    deriving Show


instance Semantics EvalSem (Literal Char) where
    sem _ (Literal c) = EChar c

instance Semantics EvalSem ExprF where
    sem _ (Cat (EStr x) (EStr y)) = EStr (x ++ y)
    sem _ (Lit (EChar x)) = EStr [x]

-- Example expression.
pattern I :: a -> Identity a
pattern I x = Identity x

exampleExpr :: Expr
exampleExpr = Cat (I (Cat (I (Lit (I (Literal 'a')))) (I (Lit (I (Literal 'b')))))) (I (Lit (I (Literal 'c'))))


main :: IO ()
main = do
    -- Pretty print.
    print $ runStringPrinter expr (I exampleExpr)
    -- Evaluate.
    print (runAnnotate expr (I exampleExpr) :: First (EvalSem Expr))

    -- Annotate
    let ann = runAnnotate expr (I exampleExpr) :: First (Annotated EvalSem Expr)
    case ann of
        First (Just (Annotated _ (Cat (Annotated a _) _))) -> print a
        _ -> putStrLn "pattern error"

    -- Parser
    print . IP.approximate . IP.applyPrefix (runGParser expr1) $ "c"
