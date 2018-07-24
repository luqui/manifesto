{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import System.IO (hSetBuffering, BufferMode(..), stdin)
import Control.Applicative

data Input = ILeft | IRight | IUp | IDown | IDelete | IInsert Char

-- When you descend into part of the tree to make an edit, it's a bit like
-- a call, where you go in there to do some work (yielding a series of views),
-- and then at some point you exit with a new version of whatever you made.

type Handler a = Input -> Maybe (Action a)

data Action a
    = Yield (View a) (Handler a)
    | Done a
    deriving (Functor)

data View a = View String a
    deriving (Functor)

(>>>=) :: Action a -> (a -> Action a) -> Action a
Yield v h >>>= f = Yield v (fmap (>>>= f) . h) 
Done x >>>= f = f x

getValue :: View a -> a
getValue (View _ x) = x

mapView :: (View a -> View a) -> Action a -> Action a
mapView f (Yield v h) = Yield (f v) (fmap (mapView f) . h)
mapView _ (Done x) = Done x

withHandler :: Action a -> (a -> Handler a) -> Action a
withHandler (Yield v h) h' = Yield v $ \i -> case h' (getValue v) i of
    Nothing -> fmap (`withHandler` h') (h i)
    Just a' -> Just a'
withHandler (Done a) _ = Done a

frame :: (a -> View a) -> (a -> Action a) -> (a -> Action a)
frame viewer subf a = Yield (viewer a) $ \case
    IDown -> Just $ subf a `withHandler` \a' -> \case
        IUp -> Just $ frame viewer subf a'
        _ -> Nothing
    _ -> Nothing

mergeHandlers :: Handler a -> Handler a -> Handler a
mergeHandlers h h' i = h i <|> h' i

infixr 5 <++>
(<++>) :: View [a] -> View [a] -> View [a]
View s xs <++> View s' xs' = View (s ++ s') (xs ++ xs')

emptyV :: String -> View [a]
emptyV s = View s []

emptyHandler :: Handler a
emptyHandler = const Nothing

cursor :: forall a. ([a] -> View [a]) -> Handler [a] -> [a] -> Action [a]
cursor viewer inserth = go []
    where
    go pre post = Yield (viewer (reverse pre) <++> emptyV "|" <++> viewer post) $ 
        mergeHandlers lrHandler insertHandler
        where
        lrHandler ILeft | p:pre' <- pre = Just $ go pre' (p:post)
        lrHandler IRight | p:post' <- post = Just $ go (p:pre) post'
        lrHandler _ = Nothing

        insertHandler :: Handler [a]
        insertHandler i = fmap doh (inserth i)
            where
            doh x = mapView ((viewer (reverse pre) <++>) . (<++> emptyV "|" <++> viewer post)) x >>>= \xs -> go (reverse xs ++ pre) post

char :: Handler Char
char (IInsert ch) = Just (Done ch)
char _ = Nothing

charS :: Handler String
charS = (fmap.fmap.fmap) (:[]) char

viewString :: String -> View String
viewString x = View x x

test :: Action String
test = frame viewString (cursor viewString charS) "hello"

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go test
  where
    go a@(Yield (View v _) h) = do
        putStrLn v
        ch <- getChar
        putStrLn ""
        let ch' = case ch of
                    'H' -> ILeft
                    'L' -> IRight
                    'J' -> IDown
                    'K' -> IUp
                    'D' -> IDelete
                    c   -> IInsert c
        maybe (go a) go (h ch')
    go (Done _) = return ()
