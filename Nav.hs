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
import Control.Applicative (Alternative(..), liftA2)

class NavInput i where
    _ILeft, _IRight, _IUp, _IDown :: L.Prism' i ()
    _IChar :: L.Prism' i Char

pattern ILeft :: (NavInput i) => i
pattern ILeft <- (L.matching _ILeft -> Right ()) where
    ILeft = L.review _ILeft ()

pattern IRight :: (NavInput i) => i
pattern IRight <- (L.matching _IRight -> Right ()) where
    IRight = L.review _IRight ()

pattern IUp :: (NavInput i) => i
pattern IUp <- (L.matching _IUp -> Right ()) where
    IUp = L.review _IUp ()

pattern IDown :: (NavInput i) => i
pattern IDown <- (L.matching _IDown -> Right ()) where
    IDown = L.review _IDown ()

pattern IChar :: (NavInput i) => Char -> i
pattern IChar c <- (L.matching _IChar -> Right c) where
    IChar c = L.review _IChar c

-- Value of an InputF is Nothing if there are no operations possible at all --
-- i.e. this is not a valid hole.  
newtype InputF i a = InputF { runInputF :: Maybe (i -> First a) }
    deriving (Functor, Semigroup, Monoid)

instance Applicative (InputF i) where
    pure = InputF . pure . pure . pure
    InputF f <*> InputF x = InputF ((liftA2.liftA2) (<*>) f x)

instance Alternative (InputF i) where
    empty = InputF mempty
    InputF a <|> InputF b = InputF ((liftA2.liftA2) (<>) a b)

newtype Nav i a = Nav { runNav :: Cofree (InputF i) a }
    deriving (Functor)

newtype FocNav i a = FocNav { runFocNav :: Nav i (Focusable a) }
    deriving (Functor)

instance (NavInput i) => Applicative (FocNav i) where
    pure = FocNav . Nav . pure . pure
    FocNav f <*> FocNav x = FocNav $ uncurry (<*>) . distribFocus <$> adjacent f x

data PDPair a b x where
    PDLeft :: b -> PDPair a b a
    PDRight :: a -> PDPair a b b

data Loc p = forall a. Loc (p a) a 

-- Loc (PDPair a b) is isomorphic to (Bool, a, b), where the bool indicates
-- which one is in focus.  But this way is hinting at a deeper level of
-- abstraction that I might find someday.
--
-- There is a problem here, and that is that it puts the focus on subtrees
-- without any `level`s.  E.g. We might focus on a trivial unit which has
-- no syntactic information.  What we want is to concatenate the collection
-- of holes using this logic, not the trees themselves.
adjacent :: (NavInput i) => Nav i a -> Nav i b -> Nav i (Loc (PDPair a b))
adjacent = \(Nav n) (Nav n') -> Nav $ leftCont n n'
    where
    leftCont (x :< InputF Nothing) ys = Loc (PDRight x) <$> ys
    leftCont (x :< InputF (Just xi)) ys = Loc (PDLeft (extract ys)) x :< 
        ((\xs -> leftCont xs ys) <$> InputF (Just xi)) <> InputF (Just (\case
            IRight -> moveRight (x :< InputF (Just xi)) ys
            _ -> mempty))

    moveRight _ (_ :< InputF Nothing) = mempty
    moveRight xs (y :< InputF (Just yi)) = pure (rightCont xs (y :< InputF (Just yi)))

    rightCont xs (y :< InputF Nothing) = Loc (PDLeft y) <$> xs
    rightCont xs (y :< InputF (Just yi)) = Loc (PDRight (extract xs)) y :< 
        ((\ys -> rightCont xs ys) <$> InputF (Just yi)) <> InputF (Just (\case
            ILeft -> moveLeft xs (y :< InputF (Just yi))
            _ -> mempty))

    moveLeft (_ :< InputF Nothing) _ = mempty
    moveLeft (x :< InputF (Just xi)) ys = pure (leftCont (x :< (InputF (Just xi))) ys)

data PDLevel a x where
    PDOutside :: PDLevel a a
    PDInside  :: PDLevel a a

level :: (NavInput i) => Nav i a -> Nav i (Loc (PDLevel a))
level (Nav n) = Nav (outsideCont n)
    where
    -- The commented variants never descend into a subtree that has no
    -- available operations.
    {-
    outsideCont (x :< InputF Nothing) = Loc PDOutside x :< InputF Nothing
    outsideCont (x :< InputF (Just xi)) = Loc PDOutside x :< InputF (Just (\case
        IDown -> pure (insideCont (x :< InputF (Just xi)))
        _ -> mempty))
    -}
    outsideCont (x :< xi) = Loc PDOutside x :< InputF (Just (\case
        IDown -> pure (insideCont (x :< xi))
        _ -> mempty))
    {-
    insideCont (x :< InputF Nothing) = Loc PDOutside x :< InputF Nothing  -- exit when there is no more input to be had inside? yes?
    insideCont (x :< InputF (Just xi)) = Loc PDInside x :< (insideCont <$> InputF (Just xi)) <> InputF (Just (\case
        IUp -> pure (outsideCont (x :< InputF (Just xi)))
        _ -> mempty))
    -}
    insideCont (x :< xi) = Loc PDInside x :< (insideCont <$> xi) <> InputF (Just (\case
        IUp -> pure (outsideCont (x :< xi))
        _ -> mempty))

levelFocus :: (a -> a) -> Loc (PDLevel (Focusable a)) -> Focusable a
levelFocus inFocus (Loc PDOutside x) Focused = inFocus (x Unfocused)
levelFocus _ (Loc PDOutside x) Unfocused = x Unfocused
levelFocus _ (Loc PDInside x) foc = x foc

levelFocNav :: (NavInput i) => (a -> a) -> FocNav i a -> FocNav i a
levelFocNav inFocus (FocNav n) = FocNav $ levelFocus inFocus <$> level n

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
string s = Nav $ render :< InputF (Just (\case
    IChar c -> pure (runNav (string (s ++ [c])))
    _ -> mempty))
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
                    "up" -> Just IUp
                    "down" -> Just IDown
                    [c] -> Just (IChar c)
                    _ -> Nothing
        maybe (putStrLn "no" >> go (x :< xs)) go $ join (getFirst . maybe (const (First Nothing)) id (runInputF xs) <$> inp) 
