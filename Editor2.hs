{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import System.IO (hSetBuffering, BufferMode(..), stdin)
import Control.Applicative

data Input = ILeft | IRight | IUp | IDown | IDelete | IInsert Char

-- When you descend into part of the tree to make an edit, it's a bit like
-- a call, where you go in there to do some work (yielding a series of views),
-- and then at some point you exit with a new version of whatever you made.

newtype Handler a = Handler { runHandler :: Input -> Maybe a }
    deriving (Functor)

instance Applicative Handler where
    pure = Handler . pure . pure
    Handler f <*> Handler g = Handler $ liftA2 (<*>) f g

instance Alternative Handler where
    empty = Handler $ pure empty
    Handler f <|> Handler g = Handler $ liftA2 (<|>) f g

data Action a
    = Yield (View a) (Handler (Action a))
    | Done a
    deriving (Functor)

data View a = View String a
    deriving (Functor)

(>>>=) :: Action a -> (a -> Action a) -> Action a
Yield v h >>>= f = Yield v (fmap (>>>= f) h) 
Done x >>>= f = f x

getValue :: View a -> a
getValue (View _ x) = x

mapView :: (View a -> View a) -> Action a -> Action a
mapView f (Yield v h) = Yield (f v) (fmap (mapView f) h)
mapView _ (Done x) = Done x

withHandler :: Action a -> (a -> Handler (Action a)) -> Action a
withHandler (Yield v h) h' = Yield v . Handler $ \i -> case runHandler (h' (getValue v)) i of
    Nothing -> fmap (`withHandler` h') (runHandler h i)
    Just a' -> Just a'
withHandler (Done a) _ = Done a

frame :: (a -> View a) -> (a -> Action a) -> (a -> Action a)
frame viewer subf a = Yield (viewer a) . Handler $ \case
    IDown -> Just $ subf a `withHandler` \a' -> Handler $ \case
        IUp -> Just $ frame viewer subf a'
        _ -> Nothing
    _ -> Nothing

infixr 5 <++>
(<++>) :: View [a] -> View [a] -> View [a]
View s xs <++> View s' xs' = View (s ++ s') (xs ++ xs')

emptyV :: String -> View [a]
emptyV s = View s []

cursor :: forall a. ([a] -> View [a]) -> Handler (Action [a]) -> [a] -> Action [a]
cursor viewer inserth = go []
    where
    go pre post = Yield (viewer (reverse pre) <++> emptyV "|" <++> viewer post) $ 
        lrHandler <|> insertHandler
        where
        lrHandler = Handler $ \case
            ILeft | p:pre' <- pre -> Just $ go pre' (p:post)
            IRight | p:post' <- post -> Just $ go (p:pre) post'
            _ -> Nothing

        insertHandler :: Handler (Action [a])
        insertHandler = fmap doh inserth
            where
            doh x = mapView ((viewer (reverse pre) <++>) . (<++> emptyV "|" <++> viewer post)) x >>>= \xs -> go (reverse xs ++ pre) post

char :: Handler (Action Char)
char = Handler $ \case
    IInsert ch -> Just (Done ch)
    _ -> Nothing

charS :: Handler (Action String)
charS = (fmap.fmap) (:[]) char

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
        maybe (go a) go (runHandler h ch')
    go (Done _) = return ()
