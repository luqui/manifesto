{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Differentiable where

import Control.Arrow (first, second)

data Loc h f a = Loc (D h f a) (f a)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class HFunctor1 h where
    hfmap1 :: (forall x. f x -> g x) -> h f a -> h g a

class (HFunctor h, HFunctor1 (D h)) => Differentiable h where
    data D h :: (* -> *) -> * -> *
    toFrames :: h f -> h (Loc h f)
    fillHole :: Loc h f a -> h f

-- A "Serial" is a differentiable functor whose holes are "in order"
class (Differentiable h) => Serial h where
    foldConst :: (Monoid m) => (b -> m) -> h (Const b) -> m
    foldConstD :: (Monoid m, Monoid n) => (b -> m) -> (b -> n) -> D h (Const b) x -> (m,n)


newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Differentiable (Field a) where
    data D (Field a) f x where
        DField :: D (Field a) f a
    toFrames (Field x) = Field (Loc DField x)
    fillHole (Loc DField x) = Field x

instance HFunctor1 (D (Field a)) where
    hfmap1 _ DField = DField

instance Serial (Field a) where
    foldConst f (Field (Const a)) = f a
    foldConstD _ _ DField = (mempty, mempty)


newtype Const a f = Const { getConst :: a }

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    data D (Const a) f x
    toFrames (Const x) = Const x
    fillHole (Loc cx _) = case cx of {}

instance HFunctor1 (D (Const a)) where
    hfmap1 _ e = case e of {}

instance Serial (Const a) where
    foldConst _ (Const _) = mempty
    foldConstD _ _ dc = case dc of {}

data (h :*: h') f = HPair (h f) (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :*: h') where
    hfmap f (HPair x y) = HPair (hfmap f x) (hfmap f y)

instance (Differentiable h, Differentiable h') => Differentiable (h :*: h') where
    data D (h :*: h') f x where
        DProductL :: D h f x -> h' f -> D (h :*: h') f x
        DProductR :: h f -> D h' f x -> D (h :*: h') f x
    toFrames (HPair x y) = 
        HPair (hfmap (\(Loc c a) -> Loc (DProductL c y) a) (toFrames x))
              (hfmap (\(Loc c a) -> Loc (DProductR x c) a) (toFrames y))
    fillHole (Loc (DProductL c y) a) = HPair (fillHole (Loc c a)) y
    fillHole (Loc (DProductR x c) a) = HPair x (fillHole (Loc c a))

instance (Differentiable h, Differentiable h') => HFunctor1 (D (h :*: h')) where
    hfmap1 f (DProductL d r) = DProductL (hfmap1 f d) (hfmap f r)
    hfmap1 f (DProductR l d) = DProductR (hfmap f l) (hfmap1 f d)

instance (Serial h, Serial h') => Serial (h :*: h') where
    foldConst f (HPair a b) = foldConst f a <> foldConst f b
    foldConstD f g (DProductL d r) = second (<> foldConst g r) (foldConstD f g d)
    foldConstD f g (DProductR l d) = first (foldConst f l <>) (foldConstD f g d)

data (h :+: h') f = HLeft (h f) | HRight (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :+: h') where
    hfmap f (HLeft x) = HLeft (hfmap f x)
    hfmap f (HRight x) = HRight (hfmap f x)

instance (Differentiable h, Differentiable h') => Differentiable (h :+: h') where
    data D (h :+: h') f x where
        DHLeft :: D h f x -> D (h :+: h') f x
        DHRight :: D h' f x -> D (h :+: h') f x
    toFrames (HLeft x) = HLeft (hfmap (\(Loc c a) -> Loc (DHLeft c) a) (toFrames x))
    toFrames (HRight x) = HRight (hfmap (\(Loc c a) -> Loc (DHRight c) a) (toFrames x))
    fillHole (Loc (DHLeft c) a) = HLeft (fillHole (Loc c a))
    fillHole (Loc (DHRight c) a) = HRight (fillHole (Loc c a))

instance (Differentiable h, Differentiable h') => HFunctor1 (D (h :+: h')) where
    hfmap1 f (DHLeft d) = DHLeft (hfmap1 f d)
    hfmap1 f (DHRight d) = DHRight (hfmap1 f d)

instance (Serial h, Serial h') => Serial (h :+: h') where
    foldConst f (HLeft a) = foldConst f a
    foldConst f (HRight b) = foldConst f b

    foldConstD f g (DHLeft a) = foldConstD f g a
    foldConstD f g (DHRight a) = foldConstD f g a
