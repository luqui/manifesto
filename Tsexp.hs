{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Control.Arrow (first)
import Data.Functor.Const (Const(..))
import Data.Monoid (Dual(..))
import Data.Constraint (Dict(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))

import Differentiable

-- A cast takes the "surface observations" of the children and gives the
-- surface observations of the parent.  The g is playing the role of keeping
-- the observations surface, that is, making sure each observation is a pure
-- composition of the observations of its children.  This allows the user of 
-- a cast to "annotate" the children arbitrarily, having those annotations
-- tracked through the cast.
type Cast h f s = forall g. h (Compose f g) -> Compose f g s

data Tsexp f s where
    Tsexp :: (Serial h) => Cast h f s -> h (Tsexp f) -> Tsexp f s
-- The first argument here is the "cast", and it is (in principle) associated
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
siblings (Zipper (CCons cx (Context1 (cast :: Cast h f a) d :: Context1 f a b)) e) 
  | Dict <- higherD @h @b
    = first getDual . foldConstD (Dual . (:[])) (:[]) $ 
        hfmap (\loc -> Const (Zipper (CCons cx (Context1 cast (fillHole loc))) e))
              (toFrames d)

synthesize :: (Functor f) => Tsexp f s -> f s
synthesize = fmap runIdentity . getCompose . go
    where
    go :: Tsexp f s -> Compose f Identity s
    go (Tsexp cast dat) = cast (hfmap go dat)


edit :: Tsexp f s -> f (Tsexp f s)
edit = getCompose . go
    where
    go :: Tsexp f s -> Compose f (Tsexp f) s
    go (Tsexp cast dat) = cast (hfmap go dat)

observe :: (Functor f) => Zipper f a -> f (Zipper f a)
observe (Zipper cx e) = Zipper cx <$> edit e


exampleExp :: Tsexp (Const String) a
exampleExp = Tsexp (\(HPair (Field (Compose (Const a))) (Field (Compose (Const b)))) -> Compose (Const (a ++ "|" ++ b))) (HPair
    (Field (Tsexp (\(Const b) -> Compose (Const (show b))) (Const True)))
    (Field (Tsexp (\(Const s) -> Compose (Const s)) (Const "boo"))))
