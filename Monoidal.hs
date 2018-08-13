{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Monoidal where

import Control.Lens (Iso', AnIso', withIso, iso)

class IsoFunctor f where
    isomap :: AnIso' a b -> Iso' (f a) (f b)

(≪$≫) :: (IsoFunctor f) => AnIso' a b -> f a -> f b
i ≪$≫ x = withIso (isomap i) (\f _ -> f x)

class (IsoFunctor f) => Monoidal f where
    unit :: f ()
    (≪*≫) :: f a -> f b -> f (a,b)

infixr 5 ≪:≫
(≪:≫) :: forall f t a b. (Monoidal f, TupleCons t a b) => f a -> f b -> f t
x ≪:≫ ys = withIso (isomap consiso) (\f _ -> f (x ≪*≫ ys))

class TupleCons t a b | t -> a b where
    consiso :: Iso' (a, b) t

instance TupleCons (a,b) a b where
    consiso = iso id id
    
instance TupleCons (a,b,c) a (b,c) where
    consiso = iso (\(a,(b,c)) -> (a,b,c)) (\(a,b,c) -> (a,(b,c)))

instance TupleCons (a,b,c,d) a (b,c,d) where
    consiso = iso (\(a,(b,c,d)) -> (a,b,c,d)) (\(a,b,c,d) -> (a,(b,c,d)))
