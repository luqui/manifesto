{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grammar where

import qualified Control.Lens as L
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Nav
import Control.Applicative (liftA2, (<|>))
import Control.Monad ((<=<))
import Data.Bifunctor (first)

import Data.Functor.Const
import Monoidal

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

instance HFunctor (Const b) where
    hfmap _ (Const x) = Const x

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
    hfmap f (Product x y) = Product (hfmap f x) (hfmap f y)

class (Monoidal g) => Grammar g where
    (≪?≫) :: L.Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

class (Grammar g) => Syntax g where
    char :: g Char
    symbol :: String -> g ()
    focus :: g a -> g a


----------------- S expression builder -----------------

data SExp a = SExp a [SExp a]
    deriving (Show, Functor)

-- This is interesting!  We flatten everything, but we don't
-- necessarily have to; Builder here could be essentially a
-- mapping between a proper a and an S-expression
-- representation thereof.
data Builder f a = Builder a [SExp (f a)]
    deriving (Functor, Show)

instance (Functor f) => Applicative (Builder f) where
    pure x = (\() -> x) <$> unit
    f <*> x = uncurry ($) <$> (f ≪*≫ x)

addFocus :: (a -> f a) -> Builder f a -> Builder f a
addFocus f (Builder x xhs) = Builder x [SExp (f x) xhs]

instance (Functor f) => IsoFunctor (Builder f)

instance (Functor f) => Monoidal (Builder f) where
    unit = Builder () []
    Builder x xhs ≪*≫ Builder y yhs
        = Builder (x,y) ((fmap.fmap.fmap) (,y) xhs ++ (fmap.fmap.fmap) (x,) yhs)


------------------- tangible values --------------------------

data View v a = View v a
    deriving (Functor)

instance (Show v) => Show (View v a) where
    show (View v _) = show v

instance (Monoid v) => Applicative (View v) where
    pure = View mempty
    View v f <*> View v' x = View (v <> v') (f x)

vConsWith :: (TupleCons t a b) => (v -> v' -> v'') -> View v a -> View v' b -> View v'' t
vConsWith f (View v x) (View v' x') = View (f v v') (L.view consiso (x,x'))

(<+>) :: (TupleCons t a b) => View (PP.Doc s) a -> View (PP.Doc s) b -> View (PP.Doc s) t
(<+>) = vConsWith (PP.<+>)


------------------- destructuring traversal -------------------

-- I'm eventually trying to compose together the type 
--
--    Editor attr a = a -> Maybe (Nav (View (PP.Doc attr) a)).
--
-- Supporting the methods
--
--    char :: g Char
--    string :: String -> g ()
--    focus :: g a -> g a
-- 
-- `View (PP.Doc attr)` has `string`. `Nav` has `focus`.  `Editor attr` has
-- `char` -- the ability to pass input to output.  But how these all fit
-- together into a coherent composition of abstractions is eluding me.
--
-- Maybe we should stop trying to be clever and just go for it directly.  We
-- can abstract away patterns later.

newtype Editor i attr a = Editor { runEditor :: a -> Maybe (Nav.FocNav i (View (PP.Doc attr) a)) }

$( L.makePrisms ''Editor )

instance IsoFunctor (Editor i attr) where
    isomap i = _Editor . L.dimapping (L.from i) (L.mapping (L.mapping (L.mapping i))) . L.from _Editor

instance (Nav.NavInput i) => Monoidal (Editor i attr) where
    unit = Editor (\() -> pure (pure (pure ())))
    Editor f ≪*≫ Editor g = Editor $ \(x,y) -> (liftA2.liftA2.liftA2) (,) (f x) (g y)

instance (Nav.NavInput i) => Grammar (Editor i attr) where
    empty = Editor (\_ -> Nothing)
    p ≪?≫ ed = Editor $ (fmap.fmap.fmap) (L.review p) . runEditor ed <=< L.preview p
    ed ≪|≫ ed' = Editor $ \x -> runEditor ed x <|> runEditor ed' x

instance (Nav.NavInput i) => Syntax (Editor i attr) where
    char = Editor (\c -> pure (pure (View (PP.pretty c) c)))
    symbol s = Editor (\u -> pure (pure (View (PP.pretty s) u)))
    focus e = Editor (\a -> Nav.levelFocNav docFoc <$> runEditor e a)
        where
        docFoc :: View (PP.Doc attr) a -> View (PP.Doc attr) a
        docFoc (View v a) = View (PP.pretty "{" <> v <> PP.pretty "}") a


_Nil :: L.Prism' [a] ()
_Nil = L.prism' (const []) (\case [] -> Just (); _ -> Nothing)

_Cons :: L.Prism [a] [b] (a,[a]) (b,[b])
_Cons = L.prism (uncurry (:)) (\case [] -> Left []; (x:xs) -> Right (x,xs))


showNode :: (Show a) => Builder (Const String) a -> Builder (Const String) a
showNode = addFocus (Const . show)

optional :: (Grammar g) => g a -> g (Maybe a)
optional g = L._Just ≪?≫ g 
         ≪|≫ L._Nothing ≪?≫ unit


many :: (Grammar g) => g a -> g [a]
many g = _Cons ≪?≫ (g ≪*≫ many g)
     ≪|≫ _Nil ≪?≫ unit

manyDelim :: (Grammar g) => g () -> g a -> g [a]
manyDelim delim g = _Cons ≪?≫ manyDelim1 delim g
                ≪|≫ _Nil ≪?≫ unit 

manyDelim1 :: (Grammar g) => g () -> g a -> g (a,[a])
manyDelim1 delim g = g ≪*≫ many (delim *≫ g)

foldrP :: L.Prism' b (a,b) -> L.Iso' b ([a],b)
foldrP p = L.iso (unfoldr (L.matching p)) 
                 (\(xs,b) -> foldr (curry (L.review p)) b xs)
                 
    where
    unfoldr :: (b -> Either b (a,b)) -> b -> ([a],b)
    unfoldr f b = 
        case f b of
            Left b' -> ([],b')
            Right (x,b') -> first (x:) (unfoldr f b')

foldlP :: L.Prism' b (b,a) -> L.Iso' b ([a],b)
foldlP p = foldrP (p . swapI) . firstI reverseI
    where
    reverseI :: L.Iso' [a] [a]
    reverseI = L.iso reverse reverse

    firstI :: L.Iso' a b -> L.Iso' (a,c) (b,c)
    firstI i = L.iso (\(a,c) -> (L.view i a, c))
                     (\(b,c) -> (L.review i b, c))

chainl1 :: (Grammar g) => g () -> L.Prism' a (a,a) -> g a -> g a
chainl1 delim prism term = L.from (foldlP prism) ≪$≫ (swapI ≪$≫ manyDelim1 delim term)

swapI :: L.Iso' (a,b) (b,a)
swapI = L.iso swap swap
    where
    swap (x,y) = (y,x)

chainr1 :: forall g a. (Grammar g) => g () -> L.Prism' a (a,a) -> g a -> g a
chainr1 delim prism term = munge ≪$≫ (term ≪*≫ (delim *≫ optional (chainl1 delim prism term)))
    where
    munge :: L.Iso' (a, Maybe a) a
    munge = L.iso (\(x,my) -> maybe x (L.review prism . (x,)) my)
                  (either (,Nothing) (\(x,y) -> (x,Just y)) . L.matching prism)

parens :: (Syntax g) => g a -> g a
parens g = symbol "(" *≫ g ≪* symbol ")"

(*≫) :: (Grammar g) => g () -> g a -> g a
s *≫ a = L.iso (\((), x) -> x) ((),) ≪$≫ (s ≪*≫ a)

(≪*) :: (Grammar g) => g a -> g () -> g a
a ≪* s = L.iso (\(x, ()) -> x) (,()) ≪$≫ (a ≪*≫ s)


