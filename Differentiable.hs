{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Differentiable where

import Control.Arrow (first, second)
import Data.Constraint (Dict(..))
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))


data Loc h f x = Loc (D h x f) (f x)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor h) => Differentiable h where
    type D h x :: (* -> *) -> *
    toFrames :: h f -> h (Loc h f)
    fillHole :: Loc h f a -> h f

    higherD :: proxy '(h,x) -> Dict (Differentiable (D h x))

-- A "Serial" is a differentiable functor whose holes are "in order"
class (Differentiable h) => Serial h where
    foldConst :: (Monoid m) => (b -> m) -> h (Const b) -> m
    foldConstD :: (Monoid m, Monoid n) => proxy '(h,x) -> (b -> m) -> (b -> n) -> D h x (Const b) -> (m,n)


newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Differentiable (Field a) where
    type D (Field a) x = DField a x
    toFrames (Field x) = Field (Loc DField x)
    fillHole (Loc DField x) = Field x
    higherD _ = Dict

instance Serial (Field a) where
    foldConst f (Field (Const a)) = f a
    foldConstD _ _ _ DField = (mempty, mempty)


data DField a x f where
    DField :: DField a a f

instance HFunctor (DField a x) where
    hfmap _ DField = DField

instance Differentiable (DField a x) where
    type D (DField a x) y = HVoid
    toFrames DField = DField
    fillHole (Loc v _) = case v of {}
    higherD _ = Dict


data HVoid f

instance HFunctor HVoid where
    hfmap _ v = case v of {}

instance Differentiable HVoid where
    type D HVoid x = HVoid
    toFrames v = case v of {}
    fillHole (Loc v _) = case v of {}
    higherD _ = Dict
    

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    type D (Const a) x = HVoid
    toFrames (Const x) = Const x
    fillHole (Loc cx _) = case cx of {}
    higherD _ = Dict

instance Serial (Const a) where
    foldConst _ (Const _) = mempty
    foldConstD _ _ _ dc = case dc of {}


data (h :*: h') f = HPair (h f) (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :*: h') where
    hfmap f (HPair x y) = HPair (hfmap f x) (hfmap f y)

instance (Differentiable h, Differentiable h') => Differentiable (h :*: h') where
    type D (h :*: h') x = (D h x :*: h') :+: (h :*: D h' x)
    toFrames (HPair x y) = 
        HPair (hfmap (\(Loc c a) -> Loc (HLeft (HPair c y)) a) (toFrames x))
              (hfmap (\(Loc c a) -> Loc (HRight (HPair x c)) a) (toFrames y))
    fillHole (Loc (HLeft (HPair c y)) a) = HPair (fillHole (Loc c a)) y
    fillHole (Loc (HRight (HPair x c)) a) = HPair x (fillHole (Loc c a))
    
    higherD (_ :: proxy '(h :*: h',x)) 
        | Dict <- higherD (Proxy :: Proxy '(h,x))
        , Dict <- higherD (Proxy :: Proxy '(h',x))
        = Dict

instance (Serial h, Serial h') => Serial (h :*: h') where
    foldConst f (HPair x y) = foldConst f x <> foldConst f y
    foldConstD (_ :: proxy '(h :*: h', x)) f g (HLeft (HPair d r)) 
        = second (<> foldConst g r) (foldConstD (Proxy :: Proxy '(h,x)) f g d)
    foldConstD (_ :: proxy '(h :*: h', x)) f g (HRight (HPair l d)) 
        = first (foldConst f l <>) (foldConstD (Proxy :: Proxy '(h',x)) f g d)
    


data (h :+: h') f = HLeft (h f) | HRight (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :+: h') where
    hfmap f (HLeft x) = HLeft (hfmap f x)
    hfmap f (HRight x) = HRight (hfmap f x)

instance (Differentiable h, Differentiable h') => Differentiable (h :+: h') where
    type D (h :+: h') x = D h x :+: D h' x
    toFrames (HLeft x) = HLeft (hfmap (\(Loc c a) -> Loc (HLeft c) a) (toFrames x))
    toFrames (HRight x) = HRight (hfmap (\(Loc c a) -> Loc (HRight c) a) (toFrames x))
    fillHole (Loc (HLeft c) a) = HLeft (fillHole (Loc c a))
    fillHole (Loc (HRight c) a) = HRight (fillHole (Loc c a))

    higherD (_ :: proxy '(h :+: h', x)) 
        | Dict <- higherD (Proxy :: Proxy '(h,x))
        , Dict <- higherD (Proxy :: Proxy '(h',x))
        = Dict

instance (Serial h, Serial h') => Serial (h :+: h') where
    foldConst f (HLeft a) = foldConst f a
    foldConst f (HRight b) = foldConst f b


    foldConstD (_ :: proxy '(h :+: h', x)) f g (HLeft a) 
        = foldConstD (Proxy :: Proxy '(h,x)) f g a
    foldConstD (_ :: proxy '(h :+: h', x)) f g (HRight a) 
        = foldConstD (Proxy :: Proxy '(h',x)) f g a

