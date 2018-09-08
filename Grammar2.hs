{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

class Shape (h :: (k -> *) -> *) where
    type h $ (f :: k -> *) :: *
    type h $ f = h f

    toShapeConstr :: h $ f -> h f
    default toShapeConstr :: (h $ f ~ h f) => h $ f -> h f
    toShapeConstr = id
    fromShapeConstr :: h f -> h $ f
    default fromShapeConstr :: (h $ f ~ h f) => h f -> h $ f
    fromShapeConstr = id

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

data Extremal a
    = Impossible
    | Indefinite
    | Definite a
    deriving (Functor, Show)

instance Semigroup (Extremal a) where
    Indefinite <> _ = Indefinite
    Impossible <> x = x
    _ <> Indefinite = Indefinite
    x <> Impossible = x
    Definite _ <> Definite _ = Indefinite

instance Monoid (Extremal a) where
    mempty = Impossible

instance Applicative Extremal where
    pure = Definite
    Impossible <*> _ = Impossible
    Indefinite <*> _ = Indefinite
    _ <*> Impossible = Impossible
    _ <*> Indefinite = Indefinite
    Definite f <*> Definite x = Definite (f x)

newtype Parser a = Parser { runParser :: String -> Extremal (String, a) }
    deriving (Functor)

instance Applicative Parser where
    pure x = Parser (\i -> pure (i, x))
    f <*> x = Parser (\i -> case runParser f i of
        Impossible -> Impossible
        Indefinite -> Indefinite
        Definite (i', f') -> fmap f' <$> runParser x i')

instance A.Alternative Parser where
    empty = Parser mempty
    a <|> b = Parser (runParser a <> runParser b)

parseSymbol :: String -> Parser ()
parseSymbol = Parser . strip
    where
    strip [] i = Definite (i, ())
    strip (_:_) [] = Definite ("", ())
    strip (s:ss) (i:is)
        | s == i = strip ss is
        | otherwise = Impossible
    

parseChar :: Parser Char
parseChar = Parser $ \case
    "" -> Indefinite
    (c:cs) -> Definite (cs,c)

eraseParser :: Parser a -> Parser ()
eraseParser p = Parser $ \i -> case runParser p i of 
    Definite (s,_) -> Definite (s,())
    Indefinite -> Definite ("", ())
    Impossible -> Impossible

newtype GParser h = GParser { runGParser :: Parser (h $ Const ()) }

instance Grammar GParser where
    p ≪?≫ gp = GParser . fmap (review p (Proxy @(Const ()))) $ runGParser gp
    unit = GParser (pure ())
    gp ≪*≫ gp' = GParser (liftA2 (,) (runGParser gp) (runGParser gp'))
    empty = GParser A.empty
    gp ≪|≫ gp' = GParser (runGParser gp A.<|> runGParser gp')

instance Syntax GParser where
    symbol s = GParser (parseSymbol s)
    char = GParser parseChar

instance Locus h GParser where
    locus gp = GParser (Const <$> eraseParser (runGParser gp))



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

newtype Incomplete = Incomplete String
    deriving (Show)

-- The abstract syntax.  Note the pattern of recusion: f on top, Identity the
-- rest of the way down.
type Expr = ExprF Identity
data ExprF f
    = Cat (f Expr) (f Expr)
    | Lit (f Char)

deriving instance Show (ExprF Identity) 
deriving instance Show (ExprF (Const ())) 

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
expr1 :: (Loci g) => g ExprF
expr1 = choice
    [ symbol "cat(" *≫ (_Cat ≪?≫ expr ≪*≫ symbol "," *≫ expr) ≪* symbol ")"
    , symbol "'" *≫ (_Lit ≪?≫ locus char) ≪* symbol "'"
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

    -- Parser
    print $ runParser (runGParser expr1) "c"
