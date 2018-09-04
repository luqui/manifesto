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

module Differentiable where

import Control.Arrow (first, second)
import Data.Constraint (Dict(..))
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))


data Loc h f x = Loc (D h x f) (f x)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor h) => Differentiable h where
    type DImpl h (x :: k) :: (k -> *) -> *
    withLocs :: h f -> h (Loc h f)
    fromLoc :: Loc h f a -> h f

    higherD :: proxy '(h,x) -> Dict (Differentiable (DImpl h x))

-- A wrapper to make D injective, because non-injective type families are a
-- pain (see `implMap` below). We don't use injective data families in the
-- first place because there is some recursive structure that we need to take
-- advantage of in order to avoid manually defining infinitely many data types.
newtype D h x f = D { getD :: DImpl h x f }

-- A "Serial" is a differentiable functor whose holes are "in order".
class (Differentiable h) => Serial h where
    foldConst :: (Monoid m) => (b -> m) -> h (Const b) -> m
    foldConstD :: (Monoid m, Monoid n) => (b -> m) -> (b -> n) -> D h x (Const b) -> (m,n)


instance (Differentiable h) => HFunctor (D h x) where
    hfmap f (D x) | Dict <- higherD (Proxy :: Proxy '(h,x)) = D (hfmap f x)

instance (Differentiable h) => Differentiable (D h x) where
    type DImpl (D h x) y = D (DImpl h x) y
    
    withLocs (D h) 
        | Dict <- higherD (Proxy :: Proxy '(h,x)) 
            = D (hfmap implMap (withLocs h))
        where
        -- Some magic I don't really care to understand for appeasing the
        -- typechecker.  Non-injective type families are a pain.
        implMap :: Loc (DImpl h x) f y -> Loc (D h x) f y
        implMap (Loc d x) = Loc (magic d) x
        magic :: D (DImpl h x) y f -> D (D h x) y f
        magic (D d) = D (D d)

    fromLoc loc 
        | Dict <- higherD (Proxy :: Proxy '(h,x))
            = D (fromLoc (implMap' loc))
        where
        implMap' :: Loc (D h x) f y -> Loc (DImpl h x) f y
        implMap' (Loc d x) = Loc (magic' d) x
        magic' :: D (D h x) y f -> D (DImpl h x) y f
        magic' (D (D d)) = D d

    -- Hard to imagine this not looping...
    higherD (_ :: proxy '(D h x,y))
        | Dict <- higherD (Proxy :: Proxy '(h,x))
        , Dict <- higherD (Proxy :: Proxy '(DImpl h x,y))
           = Dict


-- Combinators for building differentiable shape functors. 

newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Differentiable (Field a) where
    type DImpl (Field a) x = DField a x
    withLocs (Field x) = Field (Loc (D DField) x)
    fromLoc (Loc (D DField) x) = Field x
    higherD _ = Dict

instance Serial (Field a) where
    foldConst f (Field (Const a)) = f a
    foldConstD _ _ (D DField) = (mempty, mempty)


data DField a x f where
    DField :: DField a a f

instance HFunctor (DField a x) where
    hfmap _ DField = DField

instance Differentiable (DField a x) where
    type DImpl (DField a x) y = HVoid
    withLocs DField = DField
    fromLoc (Loc v _) = case v of {}
    higherD _ = Dict


data HVoid f

instance HFunctor HVoid where
    hfmap _ v = case v of {}

instance Differentiable HVoid where
    type DImpl HVoid x = HVoid
    withLocs v = case v of {}
    fromLoc (Loc v _) = case v of {}
    higherD _ = Dict
    

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    type DImpl (Const a) x = HVoid
    withLocs (Const x) = Const x
    fromLoc (Loc cx _) = case cx of {}
    higherD _ = Dict

instance Serial (Const a) where
    foldConst _ (Const _) = mempty
    foldConstD _ _ dc = case dc of {}


data (h :*: h') f = HPair (h f) (h' f)

instance (HFunctor h, HFunctor h') => HFunctor (h :*: h') where
    hfmap f (HPair x y) = HPair (hfmap f x) (hfmap f y)

instance (Differentiable h, Differentiable h') => Differentiable (h :*: h') where
    type DImpl (h :*: h') x = (D h x :*: h') :+: (h :*: D h' x)
    withLocs (HPair x y) = 
        HPair (hfmap (\(Loc c a) -> Loc (D (HLeft (HPair c y))) a) (withLocs x))
              (hfmap (\(Loc c a) -> Loc (D (HRight (HPair x c))) a) (withLocs y))
    fromLoc (Loc (D (HLeft (HPair c y))) a) = HPair (fromLoc (Loc c a)) y
    fromLoc (Loc (D (HRight (HPair x c))) a) = HPair x (fromLoc (Loc c a))
    
    higherD _ = Dict

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
    withLocs (HLeft x) = HLeft (hfmap (\(Loc c a) -> Loc (D (HLeft c)) a) (withLocs x))
    withLocs (HRight x) = HRight (hfmap (\(Loc c a) -> Loc (D (HRight c)) a) (withLocs x))
    fromLoc (Loc (D (HLeft c)) a) = HLeft (fromLoc (Loc c a))
    fromLoc (Loc (D (HRight c)) a) = HRight (fromLoc (Loc c a))

    higherD _ = Dict

instance (Serial h, Serial h') => Serial (h :+: h') where
    foldConst f (HLeft a) = foldConst f a
    foldConst f (HRight b) = foldConst f b

    foldConstD f g (D (HLeft a))
        = foldConstD f g a
    foldConstD f g (D (HRight a))
        = foldConstD f g a
