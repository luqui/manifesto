{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

import Differentiable
import Data.Functor.Identity
import Control.Arrow (first)
import Data.Monoid (Dual(..))

-- A generalized version of `h (Tsexp f) -> f (Tsexp f s)`, which also works,
-- but I think this form captures the spirit of the cast argument better.
type Cast h f s = forall i. h i -> f (i s)

data Tsexp f s where
    Tsexp :: (Serial h) => Cast h f s -> h (Tsexp f) -> Tsexp f s
-- The first argument here is the "cast", and it is in principle associated
-- with the shape alone -- the "data" of the node is all in the second
-- argument.

data Context1 f a b  where
    Context1 :: (Serial h) => Cast h f a -> D h b (Tsexp f) -> Context1 f a b

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
    foldConst (:[]) $
        hfmap (\(Loc d e) -> Const (Zipper (CCons cx (Context1 cast d)) e)) 
              (toFrames dat)

siblings :: Zipper f a -> ([Zipper f a], [Zipper f a])
siblings (Zipper CNil _) = ([], [])
siblings (Zipper (CCons cx (Context1 cast d)) exp) = 
    foldConstD (:[]) (:[]) $ 
        hfmap (\loc -> Const (Zipper (CCons cx (Context1 cast (fillHole loc))) exp))
              (toFrames d)

observe :: (Functor f) => Zipper f a -> f (Zipper f a)
observe (Zipper cx (Tsexp cast dat)) = Zipper cx <$> cast dat
