{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Control.Arrow (first)
import Data.Functor.Const (Const(..))
import Data.Monoid (Dual(..))
import Data.Constraint (Dict(..))
import Data.Functor.Compose (Compose(..))

import Differentiable

-- This is a higher-kinded version of an F-algebra, of sorts.  It takes
-- the observations of the children into the observations of the parent.
type Cast h f s = h f -> f s

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

newZipper :: Tsexp f s -> Zipper f s
newZipper = Zipper CNil

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

synthesize :: Tsexp f s -> f s
synthesize (Tsexp cast dat) = cast (hfmap synthesize dat)

-- Using the fact that one of the observations f supports gives another
-- Exp, we can edit the zipper at the current point using that observation.
editZ :: (Functor g) => (forall s. f s -> g (Tsexp f s)) -> Zipper f a -> g (Zipper f a)
editZ observe (Zipper cx e) = Zipper cx <$> observe (synthesize e)

-- Basic
data Expr 
    = Add Expr Expr
    | Lit Integer

data Obs s = Obs {
    value :: s,
    pretty :: String,
    modLit :: Maybe (Integer -> Tsexp Obs s)
  }

-- Plug this into editZ
observeModLit :: Obs s -> Compose Maybe ((->) Integer) (Tsexp Obs s)
observeModLit = Compose . modLit

toTsexp :: Expr -> Tsexp Obs Integer
toTsexp (Add x y) = Tsexp (\(HPair (Field x') (Field y')) -> Obs { value = value x' + value y', pretty = "(" ++ pretty x' ++ "+" ++ pretty y' ++ ")", modLit = Nothing }) (HPair (Field (toTsexp x)) (Field (toTsexp y)))
toTsexp (Lit z) = Tsexp (\(Field obs) -> Obs { value = value obs, pretty = pretty obs, modLit = Nothing }) (Field (toTsexpInt z))

toTsexpInt :: Integer -> Tsexp Obs Integer
toTsexpInt z = Tsexp obs (Const z)
    where
    obs :: Const Integer Obs -> Obs Integer
    obs (Const z') = Obs { value = z', pretty = show z', modLit = Just toTsexpInt }

exampleExp :: Expr
exampleExp = Add (Lit 1) (Add (Lit 2) (Lit 3))
