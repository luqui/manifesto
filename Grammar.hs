{-# OPTIONS -Wall -fno-warn-orphans #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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

module Grammar 
    ( Product(..), type (:*:)
    , Label(..), type L
    , LiteralF(..), type Literal, _Literal
    , type I, pattern I, Const(..)
    , Prism(..), type HPrism
    , Only(..)

    , Grammar(..), Locus(..), literal, (≪*), (*≫), choice

    , Syntax(..)
    , GParser(..)
    , Tree(..)
    , StringPrinter(..)
    , Annotate(..), Semantics(..)
    , Annotated(..)
    )
where

import Prelude hiding (id, (.))
import Control.Applicative (liftA2)
import qualified Control.Applicative as A
import Control.Category (Category(..))
import Control.Monad ((<=<))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Kind (Type)
import Data.Monoid (First(..))
import Rank2 (Product(..), Only(..))
import qualified Rank2

import qualified ApproximationParser as AP

-- A bit of "dialect"
type (:*:) = Product

data Label = Label ((Label -> Type) -> Type)
type L = 'Label

-- The same as Data.Functor.Const, but matching the naming pattern for
-- readability.
newtype LiteralF a f = Literal a
    deriving (Eq, Ord, Read, Show)
type Literal a = L (LiteralF a)

instance Rank2.Functor (LiteralF a) where
    _ <$> Literal a = Literal a

_Literal :: HPrism (Const a) (LiteralF a)
_Literal = Prism (\(Const x) -> Literal x) (\(Literal x) -> Just (Const x))

type I = Identity
pattern I :: a -> I a
pattern I x = Identity x

-- TODO: PR this into Rank2
instance Rank2.Functor (Const a) where
    _ <$> Const x = Const x

-- N.B. The arguments are reversed from the prism in lens.
data Prism a b = Prism { 
    review  :: a -> b,
    preview :: b -> Maybe a
  }

instance Category Prism where
    id = Prism id pure
    Prism to from . Prism to' from' = Prism (to . to') (from' <=< from)

type HPrism h h' = forall f. Prism (h f) (h' f)

infixr 4 ≪?≫
infixr 5 ≪*≫, ≪*, *≫
infixr 3 ≪|≫
-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    (≪?≫) :: HPrism h h' -> g h -> g h'
    unit  :: g (Const ())
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    empty :: g h
    (≪|≫) :: g h -> g h -> g h

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (L h))

literal :: (Locus (LiteralF a) g) => g (Const a) -> g (Only (Literal a))
literal = locus . (_Literal ≪?≫)

(*≫) :: (Grammar g) => g (Const ()) -> g h -> g h
s *≫ g = leftUnit ≪?≫ (s ≪*≫ g)
    where
    leftUnit :: HPrism (Const () :*: h) h
    leftUnit = Prism (\(Pair (Const ()) x) -> x) 
                     (\x -> Just (Pair (Const ()) x))

(≪*) :: (Grammar g) => g h -> g (Const ()) -> g h
g ≪* s = rightUnit ≪?≫ (g ≪*≫ s)
    where
    rightUnit :: HPrism (h :*: Const ()) h
    rightUnit = Prism (\(Pair x (Const ())) -> x) 
                      (\x -> Just (Pair x (Const ())))

choice :: (Grammar g) => [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Const Char)


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



data Tree :: Label -> * where
    Tree :: h Tree -> Tree (L h)

newtype StringPrinter h = StringPrinter { runStringPrinter :: h Tree -> First String }

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
    locus pp = StringPrinter (\(Only (Tree h)) -> runStringPrinter pp h)

class Semantics f h where
    sem :: h f -> f (L h)


newtype Annotate f h = Annotate { runAnnotate :: h Tree -> First (h f) }

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
    locus (Annotate ann) = Annotate (\(Only (Tree h)) -> Only . sem <$> ann h)


data Annotated f a where
    Annotated :: f (L h) -> h (Annotated f) -> Annotated f (L h)

instance (Semantics f h, Rank2.Functor h) => Semantics (Annotated f) h where
    sem hann = Annotated (sem hf) hann
        where
        hf :: h f
        hf = Rank2.fmap (\(Annotated fa _) -> fa) hann
