{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Differentiable where

import Control.Arrow (first, second)
import Data.Constraint (Dict(..))
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))


data Loc h f x = Loc (D h x f) (f x)

implMap :: Loc (DImpl h x) f y -> Loc (D h x) f y
implMap (Loc d x) = Loc (dmap d) x
    where
    dmap :: D (DImpl h x) y f -> D (D h x) y f
    dmap (D di) = D di

implMap' :: Loc (D h x) f y -> Loc (DImpl h x) f y
implMap' (Loc d x) = Loc (dmap' d) x
    where
    dmap' :: D (D h x) y f -> D (DImpl h x) y f
    dmap' (D di) = D di

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor h) => Differentiable h where
    type DImpl h (x :: k) :: (k -> *) -> *
    toFrames :: h f -> h (Loc h f)
    fillHole :: Loc h f a -> h f

    higherD' :: proxy '(h,x) -> Dict (Differentiable (DImpl h x))

newtype D h x f = D { getD :: DImpl h x f }

instance (Differentiable h) => HFunctor (D h x) where
    hfmap f (D x) | Dict <- higherD' (Proxy :: Proxy '(h,x)) = D (hfmap f x)

instance (Differentiable h) => Differentiable (D h x) where
    type DImpl (D h x) y = DImpl (DImpl h x) y
    -- toFrames :: D h x f -> D h x (Loc (D h x) f)
    -- h :: DImpl h x f
    -- toFrames h :: DImpl h x f (Loc (DImpl h x) f)
    toFrames (D h) 
        | Dict <- higherD' (Proxy :: Proxy '(h,x)) 
            = D (hfmap implMap (toFrames h))
    fillHole loc 
        | Dict <- higherD' (Proxy :: Proxy '(h,x))
            = D (fillHole (implMap' loc))

    -- Hard to imagine this not looping...
    higherD' (_ :: proxy '(D h x,y))
        | Dict <- higherD' (Proxy :: Proxy '(h,x))
        , Dict <- higherD' (Proxy :: Proxy '(DImpl h x,y))
           = Dict
    


-- A "Serial" is a differentiable functor whose holes are "in order"
class (Differentiable h) => Serial h where
    foldConst :: (Monoid m) => (b -> m) -> h (Const b) -> m
    foldConstD :: (Monoid m, Monoid n) => (b -> m) -> (b -> n) -> D h x (Const b) -> (m,n)


newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Differentiable (Field a) where
    type DImpl (Field a) x = DField a x
    toFrames (Field x) = Field (Loc (D DField) x)
    fillHole (Loc (D DField) x) = Field x
    higherD' _ = Dict

instance Serial (Field a) where
    foldConst f (Field (Const a)) = f a
    foldConstD _ _ (D DField) = (mempty, mempty)


data DField a x f where
    DField :: DField a a f

instance HFunctor (DField a x) where
    hfmap _ DField = DField

instance Differentiable (DField a x) where
    type DImpl (DField a x) y = HVoid
    toFrames DField = DField
    fillHole (Loc v _) = case v of {}
    higherD' _ = Dict


data HVoid f

instance HFunctor HVoid where
    hfmap _ v = case v of {}

instance Differentiable HVoid where
    type DImpl HVoid x = HVoid
    toFrames v = case v of {}
    fillHole (Loc v _) = case v of {}
    higherD' _ = Dict
    

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    type DImpl (Const a) x = HVoid
    toFrames (Const x) = Const x
    fillHole (Loc cx _) = case cx of {}
    higherD' _ = Dict

instance Serial (Const a) where
    foldConst _ (Const _) = mempty
    foldConstD _ _ dc = case dc of {}


data (h :*: h') f = HPair (h f) (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :*: h') where
    hfmap f (HPair x y) = HPair (hfmap f x) (hfmap f y)

instance (Differentiable h, Differentiable h') => Differentiable (h :*: h') where
    type DImpl (h :*: h') x = (D h x :*: h') :+: (h :*: D h' x)
    toFrames (HPair x y) = 
        HPair (hfmap (\(Loc c a) -> Loc (D (HLeft (HPair c y))) a) (toFrames x))
              (hfmap (\(Loc c a) -> Loc (D (HRight (HPair x c))) a) (toFrames y))
    fillHole (Loc (D (HLeft (HPair c y))) a) = HPair (fillHole (Loc c a)) y
    fillHole (Loc (D (HRight (HPair x c))) a) = HPair x (fillHole (Loc c a))
    
    higherD' _ = Dict

instance (Serial h, Serial h') => Serial (h :*: h') where
    foldConst f (HPair x y) = foldConst f x <> foldConst f y
    foldConstD f g (D (HLeft (HPair d r)))
        = second (<> foldConst g r) (foldConstD f g d)
    foldConstD f g (D (HRight (HPair l d)))
        = first (foldConst f l <>) (foldConstD f g d)
    


data (h :+: h') f = HLeft (h f) | HRight (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :+: h') where
    hfmap f (HLeft x) = HLeft (hfmap f x)
    hfmap f (HRight x) = HRight (hfmap f x)

instance (Differentiable h, Differentiable h') => Differentiable (h :+: h') where
    type DImpl (h :+: h') x = D h x :+: D h' x
    toFrames (HLeft x) = HLeft (hfmap (\(Loc c a) -> Loc (D (HLeft c)) a) (toFrames x))
    toFrames (HRight x) = HRight (hfmap (\(Loc c a) -> Loc (D (HRight c)) a) (toFrames x))
    fillHole (Loc (D (HLeft c)) a) = HLeft (fillHole (Loc c a))
    fillHole (Loc (D (HRight c)) a) = HRight (fillHole (Loc c a))

    higherD' _ = Dict

instance (Serial h, Serial h') => Serial (h :+: h') where
    foldConst f (HLeft a) = foldConst f a
    foldConst f (HRight b) = foldConst f b

    foldConstD f g (D (HLeft a))
        = foldConstD f g a
    foldConstD f g (D (HRight a))
        = foldConstD f g a

