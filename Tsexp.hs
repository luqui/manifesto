{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

import Differentiable
import Data.Functor.Identity

type Shape h = (Differentiable h, Serial h)

data Tsexp f s where
    Tsexp :: (Shape h) => (h (Tsexp f) -> f (Tsexp f s)) -> h (Tsexp f) -> Tsexp f s
-- The first argument here is the "cast", and it is in principle associated
-- with the shape alone -- the "data" of the node is all in the second
-- argument.

data Context1 f s s' where
    Context1 :: (Shape h) => (h (Tsexp f) -> f (Tsexp f s)) -> D h (Tsexp f) s' -> Context1 f s s'

data Context f a b where
    CNil  :: Context f a a
    CCons :: Context f a b -> Context1 f b c -> Context f a c

data Zipper f a where
    Zipper :: Context f a b -> Tsexp f b -> Zipper f a

fillContext1 :: Context1 f s s' -> Tsexp f s' -> Tsexp f s
fillContext1 (Context1 cast d) e = Tsexp cast (fillHole (Loc d e))

zipUpContext :: Context f a b -> Tsexp f b -> Tsexp f a
zipUpContext CNil = id
zipUpContext (CCons cx cx1) = zipUpContext cx . fillContext1 cx1

zipUp :: Zipper f a -> Tsexp f a
zipUp (Zipper cx e) = zipUpContext cx e

up :: Zipper f a -> Maybe (Zipper f a)
up (Zipper CNil _) = Nothing
up (Zipper (CCons cx cx1) e) = Just (Zipper cx (fillContext1 cx1 e))

down :: Zipper f a -> [Zipper f a]
down (Zipper cx (Tsexp cast dat)) = 
    constToList $
        hfmap (\(Loc d e) -> Const (Zipper (CCons cx (Context1 cast d)) e)) 
              (toFrames dat)

observe :: (Functor f) => Zipper f a -> f (Zipper f a)
observe (Zipper cx (Tsexp cast dat)) = Zipper cx <$> cast dat
