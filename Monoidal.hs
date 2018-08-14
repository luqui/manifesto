{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Monoidal where

import qualified Control.Lens as L

class IsoFunctor f where
    isomap :: L.Iso' a b -> L.Iso' (f a) (f b)
    default isomap :: (Functor f) => L.Iso' a b -> L.Iso' (f a) (f b)
    isomap = L.mapping

(≪$≫) :: (IsoFunctor f) => L.Iso' a b -> f a -> f b
i ≪$≫ x = L.withIso (isomap i) (\f _ -> f x)

class (IsoFunctor f) => Monoidal f where
    unit :: f ()
    (≪*≫) :: f a -> f b -> f (a,b)

infixr 5 ≪:≫
(≪:≫) :: forall f t a b. (Monoidal f, TupleCons t a b) => f a -> f b -> f t
x ≪:≫ ys = L.withIso (isomap consiso) (\f _ -> f (x ≪*≫ ys))


data (f :*: g) a = Product (f a) (g a)



class TupleCons t a b | t -> a b where
    consiso :: L.Iso' (a, b) t

instance TupleCons (a,b) a b where
    consiso = L.iso id id
    
instance TupleCons (a,b,c) a (b,c) where
    consiso = L.iso (\(a,(b,c)) -> (a,b,c)) (\(a,b,c) -> (a,(b,c)))

instance TupleCons (a,b,c,d) a (b,c,d) where
    consiso = L.iso (\(a,(b,c,d)) -> (a,b,c,d)) (\(a,b,c,d) -> (a,(b,c,d)))
