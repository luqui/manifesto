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
import Control.Applicative (liftA2, (<|>))
import Control.Comonad (Comonad(..))
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad ((<=<), join)
import Data.Bifunctor (first)
import Data.Monoid (Monoid(..), First(..))

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

vConsWith :: (TupleCons t a b) => (v -> v' -> v'') -> View v a -> View v' b -> View v'' t
vConsWith f (View v x) (View v' x') = View (f v v') (L.view consiso (x,x'))

(<+>) :: (TupleCons t a b) => View (PP.Doc s) a -> View (PP.Doc s) b -> View (PP.Doc s) t
(<+>) = vConsWith (PP.<+>)

------------------- interactive editor -----------------------


data Input = ILeft | IRight | IUp | IDown | IChar Char
    deriving (Show)

newtype InputF a = InputF { runInputF :: Input -> First a }
    deriving (Functor, Semigroup, Monoid)

newtype Nav a = Nav { runNav :: Cofree InputF a }
    deriving (Functor)

data Focused = Focused | Unfocused
    deriving (Eq,Ord,Show)

instance Semigroup Focused where
    Focused <> Focused = Focused
    _ <> _ = Unfocused

instance Monoid Focused where
    mempty = Focused  -- seems strange, but it's indeed the unit of <>

type Focusable = (->) Focused

data PDPair a b x where
    PDLeft :: b -> PDPair a b a
    PDRight :: a -> PDPair a b b

data Loc p = forall a. Loc (p a) a 

adjacent :: Nav a -> Nav b -> Nav (Loc (PDPair a b))
adjacent = \(Nav n) (Nav n') -> Nav (leftCont n n')
    where
    leftCont (x :< xi) ys = Loc (PDLeft (extract ys)) x :< 
        ((\xs -> leftCont xs ys) <$> xi) <> InputF (\case
            IRight -> pure (rightCont (x :< xi) ys)
            _ -> mempty)
    rightCont xs (y :< yi) = Loc (PDRight (extract xs)) y :< 
        ((\ys -> rightCont xs ys) <$> yi) <> InputF (\case
            ILeft -> pure (leftCont xs (y :< yi))
            _ -> mempty)

-- Ok, so we're perhaps ultimately trying to build a `Nav (Zipper a)` -- a way
-- to navigate around a's with context.  adjacent returns a partial derivative,
-- then we use combinators to reassociate as necessary.  In adjacent, a might
-- itself be a zipper, but adjacent needn't know that; however we should be
-- able to massage Loc (PDPair (Zipper a) (Zipper b)) into Zipper (a,b) 
-- (perhaps, though using Zipper twice on the left is suspect, seems more like
-- Zipper should be applied like liebniz.  Is it?)

-- Loc (f * g) 
--   =? Loc f * g + f * Loc g
-- 
-- ^ This doesn't make sense.  Loc (f * g) is a type, but f and g are functors.
-- Perhaps there is hope of a liebniz rule in the non-existential variant:
--
-- Z (f * g) a
--   = a * D (f * g) a
--   = a * (D f * g + f * D g) a
--   = a * (D f a * g a + f a * D g a)
--   = a * D f a * g a + a * f a * D g a
--   = (a * D f a * g a) + (f a * a * Z g a)
--   = (Z f * g) a + (f * Z g) a
--
-- Yep!  But now we require a monotyped focus, right?

withFocus :: Focused -> Focusable a -> Focusable a
withFocus foc x = x . (foc <>)

refocus :: Loc (PDPair (Focusable a) (Focusable b)) -> (Focusable a, Focusable b)
refocus (Loc (PDLeft b) a) = (withFocus Focused a, withFocus Unfocused b)
refocus (Loc (PDRight a) b) = (withFocus Unfocused a, withFocus Focused b)

cat :: (Semigroup m) => Nav (Focusable m) -> Nav (Focusable m) -> Nav (Focusable m)
cat m n = uncurry (<>) . refocus <$> adjacent m n

string :: String -> Nav (Focusable String)
string s = Nav $ render :< InputF (\case
    IChar c -> pure (runNav (string (s ++ [c])))
    _ -> mempty)
    where
    render Unfocused = s
    render Focused = "{" ++ s ++ "}"
       

simNav :: (Show a) => Nav (Focusable a) -> IO ()
simNav = go . runNav
    where
    go (x :< xs) = do
        print (x Focused)
        line <- getLine
        let inp = case line of
                    "left" -> Just ILeft
                    "right" -> Just IRight
                    "up" -> Just IUp
                    "down" -> Just IDown
                    [c] -> Just (IChar c)
                    _ -> Nothing
        maybe (putStrLn "no" >> go (x :< xs)) go $ join (getFirst . runInputF xs <$> inp) 


------------------- destructuring traversal -------------------


newtype Editor f a = Editor { runEditor :: a -> Maybe (f a) }

$( L.makePrisms ''Editor )

instance (Functor f) => IsoFunctor (Editor f) where
    isomap i = _Editor . L.dimapping (L.from i) (L.mapping (L.mapping i)) . L.from _Editor

instance (Applicative f) => Monoidal (Editor f) where
    unit = Editor (\() -> pure (pure ()))
    Editor f ≪*≫ Editor g = Editor $ \(x,y) -> (liftA2.liftA2) (,) (f x) (g y)

instance (Applicative f) => Grammar (Editor f) where
    empty = Editor (\_ -> Nothing)
    p ≪?≫ ed = Editor $ (fmap.fmap) (L.review p) . runEditor ed <=< L.preview p
    ed ≪|≫ ed' = Editor $ \x -> runEditor ed x <|> runEditor ed' x

instance Syntax (Editor (Const String)) where
    char = Editor (\c -> Just (Const [c]))
    symbol s = Editor (\_ -> Just (Const s))
    focus = id -- Editor . (fmap.fmap.first) (\s -> "{" ++ s ++ "}") . runEditor



_Nil :: L.Prism' [a] ()
_Nil = L.prism' (const []) (\case [] -> Just (); _ -> Nothing)

_Cons :: L.Prism [a] [b] (a,[a]) (b,[b])
_Cons = L.prism (uncurry (:)) (\case [] -> Left []; (x:xs) -> Right (x,xs))


showNode :: (Show a) => Builder (Const String) a -> Builder (Const String) a
showNode = addFocus (Const . show)

listg :: (Grammar g) => g a -> g [a]
listg g = _Nil ≪?≫ unit
      ≪|≫ _Cons ≪?≫ g ≪:≫ listg g

optional :: (Grammar g) => g a -> g (Maybe a)
optional g = L._Just ≪?≫ g 
         ≪|≫ L._Nothing ≪?≫ unit


many :: (Grammar g) => g a -> g [a]
many g = _Cons ≪?≫ (g ≪*≫ many g)
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


