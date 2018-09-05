{-# OPTIONS -Wall #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Differentiable2
    (HFunctor(..)
    , D, Loc(..), fromLoc, hfmap1Loc, hfmap2Loc, commuteDs
    , Differentiable(..)
    , HTraversable(..)
    , HFList(..)
    )  where

import Data.Functor.Compose (Compose(..))

-- Differentiation without type families!

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

newtype D h x f = D { unD :: forall g. (forall y. f y -> g y) -> g x -> h g }

instance HFunctor (D h x) where
    hfmap f (D d) = D (\t -> d (t . f))

data Loc h f x = Loc { context :: D h x f, focus :: f x }

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

--------- "Proof" that derivatives are differentiable ---------
-- (Seems a bit roundabout with this WithHole business, probably
-- can be simplified away, or perhaps h (WithHole x f) is the 
-- proper representation for D h x f in the first place.)
---------------------------------------------------------------
data WithHole x f a where
    NotHole :: f a -> WithHole x f a
    Hole :: WithHole x f x

toHoleRep :: D h x f -> h (WithHole x f)
toHoleRep (D d) = d NotHole Hole

fromHoleRep :: (HFunctor h) => h (WithHole x f) -> D h x f
fromHoleRep h = D (\f foc -> replaceHole foc (hfmap (mapHole f) h))
    where
    replaceHole :: (HFunctor h) => f x -> h (WithHole x f) -> h f
    replaceHole repl = hfmap (\case
        NotHole x -> x
        Hole -> repl)

    mapHole :: (forall y. f y -> g y) -> WithHole x f a -> WithHole x g a
    mapHole f (NotHole x) = NotHole (f x)
    mapHole _ Hole = Hole

commuteDs :: D (D h y) x f -> D (D h x) y f
commuteDs d = D (\f focf -> D (\g focg -> unD (unD d (g . f) focg) id (g focf)))

commuteHoleLoc :: Loc h (WithHole x f) y -> WithHole x (Loc (D h x) f) y
commuteHoleLoc (Loc d (NotHole fy)) = NotHole (Loc (commuteDs (fromHoleRep d)) fy)
commuteHoleLoc (Loc _ Hole) = Hole

instance (Differentiable h) => Differentiable (D h x) where
    withLocs d = fromHoleRep (hfmap commuteHoleLoc holey)
        where
        holey = withLocs (toHoleRep d)
-----------------------QED--------------------

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


-- Another try: an attempt to make fromLoc cheap in the case where h is
-- large.  Basically this just says a derivative is any HFunctor h' with a 
-- polymorphic fromLoc function.

data D' h x f where
    D' :: (HFunctor h') => h' f -> (forall g. h' g -> g x -> h g) -> D' h x f

data Loc' h f x = Loc' (D' h x f) (f x)

fromLoc' :: Loc' h f x -> h f
fromLoc' (Loc' (D' cx inj) foc) = inj cx foc

instance HFunctor (D' h x) where
    hfmap f (D' cx inj) = D' (hfmap f cx) inj

newtype Field a f = Field { getField :: f a } 
instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

withLocsExample' :: Example f -> Example (Loc' Example f)
withLocsExample' (Example a b) = 
    Example (Loc' (D' (Field b) (\(Field b') x -> Example x b')) a)
            (Loc' (D' (Field a) (\(Field a') x -> Example a' x)) b)

toHoleRep' :: D' h x f -> h (WithHole x f)
toHoleRep' (D' cx inj) = inj (hfmap NotHole cx) Hole

fromHoleRep' :: (Differentiable h) => h (WithHole x f) -> D' h x f
fromHoleRep' h = D' (fromHoleRep h) (\d foc -> fromLoc (Loc d foc))
