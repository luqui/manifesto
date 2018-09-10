{-# OPTIONS -Wall -fno-warn-orphans #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grammar where

import Control.Applicative (liftA2)
import qualified Control.Applicative as A
import Control.Monad ((<=<))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Rank2 (Product(..), Only(..))
import qualified Rank2

import qualified ApproximationParser as AP

-- A bit of "dialect"
type (:*:) = Product

-- The same as Data.Functor.Const, but matching the naming pattern for
-- readability.
newtype LiteralF a f = Literal a
    deriving (Eq, Ord, Read, Show)
type Literal a = LiteralF a Identity

instance Rank2.Functor (LiteralF a) where
    _ <$> Literal a = Literal a

_Literal :: HPrism (LiteralF a) (Const a)
_Literal = Prism (\(Const x) -> Literal x) (\(Literal x) -> Just (Const x))

-- TODO: PR this into Rank2
instance Rank2.Functor (Const a) where
    _ <$> Const x = Const x

data Prism b a = Prism { 
    review  :: a -> b,
    preview :: b -> Maybe a
  }

type HPrism h' h = forall f. Prism (h' f) (h f)

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
    leftUnit = Prism (\(Pair (Const ()) x) -> x) 
                     (\x -> Just (Pair (Const ()) x))

(≪*) :: (Grammar g) => g h -> g (Const ()) -> g h
g ≪* s = rightUnit ≪?≫ (g ≪*≫ s)
    where
    rightUnit :: HPrism h (h :*: Const ())
    rightUnit = Prism (\(Pair x (Const ())) -> x) 
                      (\x -> Just (Pair x (Const ())))

choice :: (Grammar g) => [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Const Char)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h Identity))


newtype GParser h = GParser { runGParser :: AP.Parser (h (Const ())) }

instance Grammar GParser where
    p ≪?≫ gp = GParser . fmap (review p) $ runGParser gp
    unit = GParser (pure (Const ()))
    gp ≪*≫ gp' = GParser (liftA2 Pair (runGParser gp) (runGParser gp'))
    empty = GParser A.empty
    gp ≪|≫ gp' = GParser (runGParser gp A.<|> runGParser gp')

instance Syntax GParser where
    symbol s = GParser (Const <$> AP.symbol s)
    char = GParser (Const <$> AP.char)

instance Locus h GParser where
    locus gp = GParser (Only . Const <$> AP.erase (runGParser gp))


newtype StringPrinter h = StringPrinter { runStringPrinter :: h Identity -> First String }

instance Grammar StringPrinter where
    p ≪?≫ pp = StringPrinter (runStringPrinter pp <=< First . preview p)
    unit = StringPrinter (\(Const ()) -> pure "")
    pp ≪*≫ pp' = StringPrinter (\(Pair h h') -> liftA2 (<>) (runStringPrinter pp h) (runStringPrinter pp' h'))
    empty = StringPrinter (\_ -> mempty)
    pp ≪|≫ pp' = StringPrinter (\h -> runStringPrinter pp h <> runStringPrinter pp' h)

instance Syntax StringPrinter where
    symbol s = StringPrinter (\(Const ()) -> pure s)
    char = StringPrinter (\(Const c) -> pure [c])

instance Locus h StringPrinter where
    locus pp = StringPrinter (\(Only (Identity h)) -> runStringPrinter pp h)

class Semantics f h where
    sem :: h f -> f (h Identity)

newtype Annotate f h = Annotate { runAnnotate :: h Identity -> First (h f) }

instance Grammar (Annotate f) where
    p ≪?≫ ann = Annotate (fmap (review p) . runAnnotate ann <=< First . preview p)
    unit = Annotate (\(Const ()) -> pure (Const ()))
    ann ≪*≫ ann' = Annotate (\(Pair h h') -> liftA2 Pair (runAnnotate ann h) (runAnnotate ann' h'))
    empty = Annotate (\_ -> mempty)
    ann ≪|≫ ann' = Annotate (\h -> runAnnotate ann h <> runAnnotate ann' h)
    -- This is almost exactly the same as StringPrinter above.  How can we automate this?
    -- Only Identity `Rank2.Arrow` Compose First (Only f)

instance Syntax (Annotate f) where
    symbol = const unit
    char = Annotate (\(Const c) -> pure (Const c))

-- When we are annotating with f, we can only have loci on shapes that have
-- a defined semantics for f.
instance (Semantics f h) => Locus h (Annotate f) where
    locus (Annotate ann) = Annotate (\(Only (Identity h)) -> Only . sem <$> ann h)


data Annotated f a where
    Annotated :: f (h Identity) -> h (Annotated f) -> Annotated f (h Identity)

instance (Semantics f h, Rank2.Functor h) => Semantics (Annotated f) h where
    sem hann = Annotated (sem hf) hann
        where
        hf :: h f
        hf = Rank2.fmap (\(Annotated fa _) -> fa) hann

-- The abstract syntax.  Note the pattern of recusion: f on top, Identity the
-- rest of the way down.
type Expr = ExprF Identity
data ExprF f
    = Cat (f Expr) (f Expr)
    | Lit (f (Literal Char))

instance Rank2.Functor ExprF where
    f <$> Cat a b = Cat (f a) (f b)
    f <$> Lit c = Lit (f c)

deriving instance Show (ExprF Identity) 
deriving instance Show (ExprF (Const ())) 


-- These should be automatically generated.
_Cat :: HPrism ExprF (Only Expr :*: Only Expr)
_Cat = Prism (\(Pair (Only a) (Only b)) -> Cat a b)
             (\case Cat a b -> Just (Pair (Only a) (Only b))
                    _ -> Nothing)

_Lit :: HPrism ExprF (Only (Literal Char))
_Lit = Prism (\(Only c) -> Lit c)
             (\case Lit c -> Just (Only c)
                    _ -> Nothing)

-- The grammar.
-- We collect the types that need to be given semantics into the synonym 'Loci'.
type Loci g = (Syntax g, Locus ExprF g, Locus (LiteralF Char) g)

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
data instance EvalSem (Literal Char) = EChar Char
    deriving Show
data instance EvalSem Expr = EStr String
    deriving Show


instance Semantics EvalSem (LiteralF Char) where
    sem (Literal c) = EChar c

instance Semantics EvalSem ExprF where
    sem (Cat (EStr x) (EStr y)) = EStr (x ++ y)
    sem (Lit (EChar x)) = EStr [x]

-- Example expression.
pattern I :: a -> Identity a
pattern I x = Identity x

exampleExpr :: Expr
exampleExpr = Cat (I (Cat (I (Lit (I (Literal 'a')))) (I (Lit (I (Literal 'b')))))) (I (Lit (I (Literal 'c'))))


main :: IO ()
main = do
    -- Pretty print.
    print $ runStringPrinter expr (Only (I exampleExpr))
    -- Evaluate.
    print (fromOnly <$> runAnnotate expr (Only (I exampleExpr)) :: First (EvalSem Expr))

    -- Annotate
    let ann = fromOnly <$> runAnnotate expr (Only (I exampleExpr)) :: First (Annotated EvalSem Expr)
    case ann of
        First (Just (Annotated _ (Cat (Annotated a _) _))) -> print a
        _ -> putStrLn "pattern error"

    -- Parser
    print . AP.approximate . AP.applyPrefix (runGParser expr1) $ "cat("
