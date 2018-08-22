{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Nav where

import qualified Control.Lens as L
import Data.Monoid (First(..))
import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad (join)

class NavInput i where
    _ILeft :: L.Prism' i ()
    _IRight :: L.Prism' i ()
    _IChar :: L.Prism' i Char

pattern ILeft :: (NavInput i) => i
pattern ILeft <- (L.matching _ILeft -> Right ()) where
    ILeft = L.review _ILeft ()

pattern IRight :: (NavInput i) => i
pattern IRight <- (L.matching _IRight -> Right ()) where
    IRight = L.review _IRight ()

pattern IChar :: (NavInput i) => Char -> i
pattern IChar c <- (L.matching _IChar -> Right c) where
    IChar c = L.review _IChar c

newtype InputF i a = InputF { runInputF :: i -> First a }
    deriving (Functor, Semigroup, Monoid)

newtype Nav i a = Nav { runNav :: Cofree (InputF i) a }
    deriving (Functor)


data PDPair a b x where
    PDLeft :: b -> PDPair a b a
    PDRight :: a -> PDPair a b b

data Loc p = forall a. Loc (p a) a 

-- Loc (PDPair a b) is isomorphic to (Bool, a, b), where the bool indicates
-- which one is in focus.  But this way is hinting at a deeper  level of
-- abstraction that I might find someday.
adjacent :: (NavInput i) => Nav i a -> Nav i b -> Nav i (Loc (PDPair a b))
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


data Focused = Focused | Unfocused
    deriving (Eq,Ord,Show)

instance Semigroup Focused where
    Focused <> Focused = Focused
    _ <> _ = Unfocused

instance Monoid Focused where
    mempty = Focused  -- seems strange, but it's indeed the unit of <>

type Focusable = (->) Focused

withFocus :: Focused -> Focusable a -> Focusable a
withFocus foc x = x . (foc <>)


distribFocus :: Loc (PDPair (Focusable a) (Focusable b)) -> (Focusable a, Focusable b)
distribFocus (Loc (PDLeft b) a) = (withFocus Focused a, withFocus Unfocused b)
distribFocus (Loc (PDRight a) b) = (withFocus Unfocused a, withFocus Focused b)

cat :: (Semigroup m, NavInput i) => Nav i (Focusable m) -> Nav i (Focusable m) -> Nav i (Focusable m)
cat m n = uncurry (<>) . distribFocus <$> adjacent m n

string :: (NavInput i) => String -> Nav i (Focusable String)
string s = Nav $ render :< InputF (\case
    IChar c -> pure (runNav (string (s ++ [c])))
    _ -> mempty)
    where
    render Unfocused = s
    render Focused = "{" ++ s ++ "}"
       

simNav :: (NavInput i, Show a) => Nav i (Focusable a) -> IO ()
simNav = go . runNav
    where
    go (x :< xs) = do
        print (x Focused)
        line <- getLine
        let inp = case line of
                    "left" -> Just ILeft
                    "right" -> Just IRight
                    [c] -> Just (IChar c)
                    _ -> Nothing
        maybe (putStrLn "no" >> go (x :< xs)) go $ join (getFirst . runInputF xs <$> inp) 
