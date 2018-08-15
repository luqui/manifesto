{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Interactive where

import Data.Functor.Compose

data Step f a
    = Step a (f a)
    | Done a
    deriving (Functor)

instance (Applicative f) => Applicative (Step f) where
    pure = Done
    Done f <*> xs = f <$> xs
    fs <*> Done x = ($ x) <$> fs
    Step f fs <*> Step x xs = Step (f x) (fs <*> xs)

newtype Interactive m a = Interactive { runInteractive :: Step (Compose m (Interactive m)) a }
    deriving (Functor, Applicative)

step :: a -> m (Interactive m a) -> Interactive m a
step x xs = Interactive (Step x (Compose xs))

runStep :: Interactive m a -> (a, Maybe (m (Interactive m a)))
runStep (Interactive (Step x (Compose xs))) = (x, Just xs)
runStep (Interactive (Done x)) = (x, Nothing)
