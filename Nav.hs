{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Nav where

import qualified Control.Lens as L
import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad (join)
import Control.Applicative (Alternative(..), liftA2)
import Data.Functor.Compose (Compose(..))



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

data ActionF a
    = Exit a
    | Continue a
    deriving (Functor)

newtype ILog = ILog String
instance Semigroup ILog where
    ILog a <> ILog b = ILog (a ++ "|" ++ b)
instance Monoid ILog where
    mempty = ILog "[]"
instance Show ILog where
    show (ILog s) = s

newtype RequestInput i a = Req { getReq :: Compose ((,) ILog) ((->) i) a }
    deriving (Functor, Applicative)

pattern RequestInput :: String -> (i -> a) -> RequestInput i a
pattern RequestInput s f = Req (Compose (ILog s, f))

newtype InputF i a = InputF { runInputF :: Compose Maybe (Compose (RequestInput i) Maybe) a }
    deriving (Functor)

instance Semigroup (InputF i a) where
    InputF (Compose Nothing) <> b = b
    a <> InputF (Compose Nothing) = a
    InputF (Compose (Just (Compose a))) <> InputF (Compose (Just (Compose b))) = InputF (Compose (Just (Compose (liftA2 (<|>) a b))))

instance Monoid (InputF i a) where
    mempty = InputF (Compose Nothing)

newtype NavF i a = NavF { runNavF :: Compose (InputF i) ActionF a }
    deriving (Functor)

instance Semigroup (NavF i a) where
    NavF (Compose x) <> NavF (Compose y) = NavF (Compose (x <> y))

instance Monoid (NavF i a) where
    mempty = NavF (Compose mempty)



pattern NoInput :: NavF i a
pattern NoInput = NavF (Compose (InputF (Compose Nothing)))

pattern InputHook :: RequestInput i (Maybe (ActionF a)) -> NavF i a
pattern InputHook f = NavF (Compose (InputF (Compose (Just (Compose f)))))

exitHook :: (a -> b) -> NavF i a -> RequestInput i (a -> Maybe (ActionF b)) -> NavF i b
exitHook _ NoInput _ = NoInput
exitHook t (InputHook (RequestInput s ih)) (RequestInput s' ih') = 
    InputHook (RequestInput (s ++ "?" ++ s') (\i -> case ih i of
        Just (Exit a') -> ih' i a'
        a -> (fmap.fmap) t a)) 
exitHook _ _ _ = error "impossible"


newtype Nav i a = Nav { runNav :: Cofree (NavF i) a }
    deriving (Functor)

newtype FocNav i a = FocNav { runFocNav :: Nav i (Focusable a) }
    deriving (Functor)

instance (NavInput i) => Applicative (FocNav i) where
    pure x = FocNav (Nav (pure x :< NavF (Compose mempty)))
    FocNav f <*> FocNav x = FocNav $ uncurry (<*>) . distribFocus <$> adjacent f x

data PDPair a b x where
    PDLeft :: b -> PDPair a b a
    PDRight :: a -> PDPair a b b

data Loc p = forall a. Loc (p a) a 

-- Loc (PDPair a b) is isomorphic to (Bool, a, b), where the bool indicates
-- which one is in focus.  But this way is hinting at a deeper level of
-- abstraction that I might find someday.
adjacent :: (NavInput i) => Nav i a -> Nav i b -> Nav i (Loc (PDPair a b))
adjacent = \(Nav n) (Nav n') -> Nav $ leftCont n n'
    where
    (x :< NoInput) `leftCont` ys = Loc (PDRight x) <$> ys
    (x :< xi) `leftCont` ys =
        Loc (PDLeft (extract ys)) x :< 
            (exitHook (`leftCont` ys) xi $ RequestInput "adjacent left" (\case
                IRight -> \xs' -> (xs' `moveRight` ys)
                ILeft -> \xs' -> pure (Exit (xs' `leftCont` ys))
                IUp -> \xs' -> pure (Exit (xs' `leftCont` ys))
                _ -> \_ -> empty))

    moveRight xs (y :< NoInput) = pure (Exit (Loc (PDLeft y) <$> xs))
    moveRight xs (y :< yi) = (pure.Continue) (xs `rightCont` (y :< yi))

    xs `rightCont` (y :< NoInput) = Loc (PDLeft y) <$> xs
    xs `rightCont` (y :< yi) =
        Loc (PDRight (extract xs)) y :<
            (exitHook (xs `rightCont`) yi $ RequestInput "adjacent right" (\case
                ILeft -> \ys' -> (xs `moveLeft` ys')
                IRight -> \ys' -> pure (Exit (xs `leftCont` ys'))
                IUp -> \ys' -> pure (Exit (xs `leftCont` ys'))
                _ -> \_ -> empty))
    
    moveLeft (x :< NoInput) ys = pure (Exit (Loc (PDRight x) <$> ys))
    moveLeft (x :< xi) ys = (pure.Continue) ((x :< xi) `leftCont` ys)


data PDLevel a x where
    PDOutside :: PDLevel a a
    PDInside  :: PDLevel a a

level :: (NavInput i) => Nav i a -> Nav i (Loc (PDLevel a))
level (Nav n) = Nav (outsideCont n)
    where
    outsideCont (x :< xi) = Loc PDOutside x :< InputHook (RequestInput "level outside" (\case
        IDown -> (pure.Continue) (insideCont (x :< xi))
        ILeft -> pure (Exit (outsideCont (x :< xi)))
        IRight -> pure (Exit (outsideCont (x :< xi)))
        IUp -> pure (Exit (outsideCont (x :< xi)))
        _ -> empty))
    insideCont (x :< xi) = Loc PDInside x :< 
        (exitHook insideCont xi $ RequestInput "level outer" (\case
            IUp -> \xs' -> (pure.Continue) (outsideCont xs')
            _ -> \_ -> empty))

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

{-
string :: (NavInput i) => String -> Nav i (Focusable String)
string s = Nav $ render :< InputF (Just (\case
    IChar c -> pure (runNav (string (s ++ [c])))
    _ -> mempty))
    where
    render Unfocused = s
    render Focused = "{" ++ s ++ "}"
-}
       

simNav :: (NavInput i, Show a) => Nav i (Focusable a) -> IO ()
simNav = go . runNav
    where
    go (x :< xs) = do
        print (x Focused)
        case xs of
            NoInput -> putStrLn "no input accepted"
            InputHook (RequestInput s ih) -> do
                putStr $ show s ++ "> "
                line <- getLine
                let inp = case line of
                            "left" -> Just ILeft
                            "right" -> Just IRight
                            "up" -> Just IUp
                            "down" -> Just IDown
                            [c] -> Just (IChar c)
                            _ -> Nothing
                case join $ fmap ih inp of
                    Nothing -> putStrLn "invalid" >> go (x :< xs)
                    Just (Exit _) -> putStrLn "exited"
                    Just (Continue a) -> go a
            _ -> error "impossible"
