{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Differentiable2
    (HFunctor(..)
    , D, Loc(..), fromLoc, hfmap1Loc, hfmap2Loc
    , Differentiable(..)
    , HTraversable(..)
    , HFList(..)
    )  where

import Data.Functor.Compose (Compose(..))

-- Differentiation without type families!

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

newtype D h x f = D (forall g. (forall y. f y -> g y) -> g x -> h g)

instance HFunctor (D h x) where
    hfmap f (D d) = D (\t -> d (t . f))

data Loc h f x = Loc (D h x f) (f x)

fromLoc :: Loc h f a -> h f
fromLoc (Loc (D d) foc) = d id foc

hfmap1Loc :: (forall y. f y -> g y) -> Loc h f x -> Loc h g x
hfmap1Loc f (Loc d foc) = Loc (hfmap f d) (f foc)

hfmap2Loc :: (forall y. h y -> h' y) -> Loc h f x -> Loc h' f x
hfmap2Loc f (Loc (D d) foc) = Loc (D (\f' x -> f (d f' x))) foc

-- Loc h f x  ----hfmap1Loc---->  Loc h f' x
--    |                               |
--  fromLoc                        fromLoc
--    v                               v
--   h f      ----hfmap-------->     h f'

class (HFunctor h) => Differentiable h where
    withLocs :: h f -> h (Loc h f)

class (HFunctor h) => HTraversable h where
    hsequenceA :: (Applicative f) => h (Compose f g) -> f (h g)
    hsequenceA = htraverse getCompose
    htraverse :: (Applicative f) => (forall x. a x -> f (b x)) -> h a -> f (h b)
    htraverse f h = hsequenceA (hfmap (Compose . f) h)
    {-# MINIMAL hsequenceA | htraverse #-}

-- Conjecture: every HTraversable is Differentiable
-- withLocsHTraversable :: (HTraversable h) => h f -> h (Loc h f)
--
-- But HTraversable might need to be strengthened to allow type-changing applicatives.


data HFList ts f where
    HHNil :: HFList '[] f
    HHCons :: f x -> HFList xs f -> HFList (x ': xs) f

instance HFunctor (HFList ts) where
    hfmap _ HHNil = HHNil
    hfmap f (HHCons x xs) = HHCons (f x) (hfmap f xs)

instance HTraversable (HFList ts) where
    htraverse _ HHNil = pure HHNil
    htraverse f (HHCons x xs) = HHCons <$> f x <*> htraverse f xs

instance Differentiable (HFList ts) where
    withLocs HHNil = HHNil
    withLocs (HHCons x xs) = 
        HHCons (Loc (D (\f foc -> HHCons foc (hfmap f xs))) x)
               (hfmap (\(Loc d foc) -> Loc (dcons x d) foc) (withLocs xs))

dcons :: f x -> D (HFList xs) y f -> D (HFList (x ': xs)) y f
dcons x (D d) = D (\f foc -> HHCons (f x) (d f foc))


data Example f = Example (f Int) (f String)

instance HFunctor Example where
    hfmap f (Example a b) = Example (f a) (f b)

instance Differentiable Example where
    withLocs (Example a b) = 
        Example (Loc (D (\f foc -> Example foc (f b))) a)
            (Loc (D (\f foc -> Example (f a) foc)) b)

instance HTraversable Example where
    htraverse f (Example a b) = Example <$> f a <*> f b
