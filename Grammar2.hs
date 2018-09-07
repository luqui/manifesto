{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Grammar2 where

import Control.Applicative (liftA2)
import Control.Lens (Prism', Iso', iso, preview, review)
import Control.Monad ((<=<))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Rank2 (Product(..), Only(..))

type (:*:) = Product

-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    (≪?≫) :: (forall f. Prism' (h' f) (h f)) -> g h -> g h'
    unit  :: g (Const ())
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    empty :: g h
    (≪|≫) :: g h -> g h -> g h

(*≫) :: (Grammar g) => g (Const ()) -> g h -> g h
s *≫ g = leftUnit ≪?≫ (s ≪*≫ g)
    where
    leftUnit :: Iso' (h f) ((Const () :*: h) f)
    leftUnit = iso (\x -> Pair (Const ()) x) (\(Pair (Const ()) x) -> x) 

(≪*) :: (Grammar g) => g h -> g (Const ()) -> g h
g ≪* s = rightUnit ≪?≫ (g ≪*≫ s)
    where
    rightUnit :: Iso' (h f) ((h :*: Const ()) f)
    rightUnit = iso (\x -> Pair x (Const ())) (\(Pair x (Const ())) -> x) 

choice :: (Grammar g) => [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Const Char)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h Identity))

{-
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }
newtype GParser h = GParser { runGParser :: Parser (h Parser) }

instance Grammar Parser where
instance Locus h Parser
-}

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
    sem :: h f -> Only (h Identity) f

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
    locus (Annotate ann) = Annotate (\(Only (Identity h)) -> sem <$> ann h)




{-

expr :: (Locus ExprF g) => g (Only Expr)
expr = locus $ choice [
    _Add ≪?≫ expr ≪*≫ expr,
    _Lit ≪?≫ integer
  ] 

integer :: (Grammar g) => g (Only Integer)
integer = ...


-- For a more complex grammar, we should collect the loci into transitive closures
-- of what we need, e.g.
-- 
-- type Loci g = (Locus ExprF g, Locus DefnF g, Locus TypeF g)
--
-- Then most of our grammars will have signatures like
--
-- foo :: (Loci g) => g (Only Foo)
--
-- Which is about as concise as one could hope for.
-}
