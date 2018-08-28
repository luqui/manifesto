{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Differentiable where

import Control.Arrow (first, second)
import Data.Constraint.Forall
import Data.Constraint ((:-)(..), Dict(..))


data NatIso f g = NatIso (forall x. f x -> g x) (forall x. g x -> f x)

inverse :: NatIso f g -> NatIso g f
inverse (NatIso f g) = NatIso g f

apply :: NatIso f g -> f x -> g x
apply (NatIso f _) = f

data Loc h f x = Loc (D h x f) (f x)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor h, ForallF HFunctor (D h)) => Differentiable h where
    data D h :: * -> (* -> *) -> *
    toFrames :: h f -> h (Loc h f)
    fillHole :: Loc h f a -> h f

    -- Provide an alternative representation for the derivative, which is
    -- itself differentiable.  This is so we can do higher-order derivatives
    -- without getting the constraint system all in a bundle.
    derivIso :: (forall t. Differentiable t => NatIso (D h x) t -> r) -> r

-- A "Serial" is a differentiable functor whose holes are "in order"
class (Differentiable h) => Serial h where
    foldConst :: (Monoid m) => (b -> m) -> h (Const b) -> m
    foldConstD :: (Monoid m, Monoid n) => (b -> m) -> (b -> n) -> D h x (Const b) -> (m,n)


newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Differentiable (Field a) where
    data D (Field a) x f where
        DField :: D (Field a) a f
    toFrames (Field x) = Field (Loc DField x)
    fillHole (Loc DField x) = Field x

instance HFunctor (D (Field a) x) where
    hfmap _ DField = DField

instance Serial (Field a) where
    foldConst f (Field (Const a)) = f a
    foldConstD _ _ DField = (mempty, mempty)


newtype Const a f = Const { getConst :: a }

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    data D (Const a) x f
    toFrames (Const x) = Const x
    fillHole (Loc cx _) = case cx of {}

instance HFunctor (D (Const a) x) where
    hfmap _ e = case e of {}

instance Serial (Const a) where
    foldConst _ (Const _) = mempty
    foldConstD _ _ dc = case dc of {}

data (h :*: h') f = HPair (h f) (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :*: h') where
    hfmap f (HPair x y) = HPair (hfmap f x) (hfmap f y)

instance (Differentiable h, Differentiable h') => Differentiable (h :*: h') where
    data D (h :*: h') x f where
        DProductL :: D h x f -> h' f -> D (h :*: h') x f
        DProductR :: h f -> D h' x f -> D (h :*: h') x f
    toFrames (HPair x y) = 
        HPair (hfmap (\(Loc c a) -> Loc (DProductL c y) a) (toFrames x))
              (hfmap (\(Loc c a) -> Loc (DProductR x c) a) (toFrames y))
    fillHole (Loc (DProductL c y) a) = HPair (fillHole (Loc c a)) y
    fillHole (Loc (DProductR x c) a) = HPair x (fillHole (Loc c a))

instance (Differentiable h, Differentiable h') => HFunctor (D (h :*: h') x) where
    hfmap f (DProductL d r) | Sub Dict <- instF @HFunctor @(D h) @x
        = DProductL (hfmap f d) (hfmap f r)
    hfmap f (DProductR l d) | Sub Dict <- instF @HFunctor @(D h') @x
        = DProductR (hfmap f l) (hfmap f d)

instance (Serial h, Serial h') => Serial (h :*: h') where
    foldConst f (HPair a b) = foldConst f a <> foldConst f b
    foldConstD f g (DProductL d r) = second (<> foldConst g r) (foldConstD f g d)
    foldConstD f g (DProductR l d) = first (foldConst f l <>) (foldConstD f g d)

data (h :+: h') f = HLeft (h f) | HRight (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :+: h') where
    hfmap f (HLeft x) = HLeft (hfmap f x)
    hfmap f (HRight x) = HRight (hfmap f x)

instance (Differentiable h, Differentiable h') => Differentiable (h :+: h') where
    data D (h :+: h') x f where
        DHLeft :: D h x f -> D (h :+: h') x f
        DHRight :: D h' x f -> D (h :+: h') x f
    toFrames (HLeft x) = HLeft (hfmap (\(Loc c a) -> Loc (DHLeft c) a) (toFrames x))
    toFrames (HRight x) = HRight (hfmap (\(Loc c a) -> Loc (DHRight c) a) (toFrames x))
    fillHole (Loc (DHLeft c) a) = HLeft (fillHole (Loc c a))
    fillHole (Loc (DHRight c) a) = HRight (fillHole (Loc c a))

instance (Differentiable h, Differentiable h') => HFunctor (D (h :+: h') x) where
    hfmap f (DHLeft d) | Sub Dict <- instF @HFunctor @(D h) @x
        = DHLeft (hfmap f d)
    hfmap f (DHRight d) | Sub Dict <- instF @HFunctor @(D h') @x
        = DHRight (hfmap f d)

instance (Serial h, Serial h') => Serial (h :+: h') where
    foldConst f (HLeft a) = foldConst f a
    foldConst f (HRight b) = foldConst f b

    foldConstD f g (DHLeft a) = foldConstD f g a
    foldConstD f g (DHRight a) = foldConstD f g a
