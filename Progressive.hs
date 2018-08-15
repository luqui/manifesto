{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Progressive where

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

newtype Progressive m a = Progressive { runProgressive :: Step (Compose m (Progressive m)) a }
    deriving (Functor, Applicative)

step :: a -> m (Progressive m a) -> Progressive m a
step x xs = Progressive (Step x (Compose xs))

runStep :: Progressive m a -> (a, Maybe (m (Progressive m a)))
runStep (Progressive (Step x (Compose xs))) = (x, Just xs)
runStep (Progressive (Done x)) = (x, Nothing)
