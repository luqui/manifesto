{-# OPTIONS -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans -fdefer-type-errors #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Functor.Differentiable.Rank2
    ( D(..), mapShapeD
    , Loc(..), fromLoc, fill, mapShapeLoc, mapLoc
    , Differentiable(..)
    , DFoldable(..)
    , commuteDs
    )
where

import qualified Rank2
import Data.Monoid (Endo(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Compose (Compose(..))

-- TODO: PR these into Rank2
-- <$> should have the same precedence as the built in one, dude
instance Rank2.Functor (Const x) where
    _ <$> Const x = Const x

instance Rank2.Foldable (Const x) where
    foldMap _ = mempty

instance Rank2.Traversable (Const x) where
    sequence (Const x) = pure (Const x)

instance (Functor f, Rank2.Functor h) => Rank2.Functor (Compose f h) where
    f <$> Compose x = Compose ((f Rank2.<$>) <$> x)


data D h x f where
    D :: (Rank2.Functor h') => h' f -> (forall g. h' g -> g x -> h g) -> D h x f

instance Rank2.Functor (D h x) where
    f <$> D cx inj = D (f Rank2.<$> cx) inj

mapShapeD :: (forall g. h g -> h' g) -> D h x f -> D h' x f
mapShapeD f (D cx inj) = D cx (\h' pt -> f (inj h' pt))

data Loc h f x = Loc { context :: D h x f, focus :: f x }

fromLoc :: Loc h f x -> h f
fromLoc (Loc d pt) = fill d pt

fill :: D h x f -> f x -> h f
fill (D cx inj) pt = inj cx pt

mapShapeLoc :: (forall g. h g -> h' g) -> Loc h f x -> Loc h' f x
mapShapeLoc f (Loc d pt) = Loc (mapShapeD f d) pt

mapLoc :: (forall y. f y -> f' y) -> Loc h f x -> Loc h f' x
mapLoc f (Loc d pt) = Loc (f Rank2.<$> d) (f pt)

embedLocs :: (Rank2.Functor h) => (forall x. h x -> t x) -> h (Loc h f) -> t (Loc t f)
embedLocs f x = f (mapShapeLoc f Rank2.<$> x)

class (Rank2.Functor h) => Differentiable h where
    withLocs :: h f -> h (Loc h f)

instance Differentiable (Const x) where
    withLocs (Const x) = Const x

instance Differentiable (Rank2.Only f) where
    withLocs (Rank2.Only x) = 
        Rank2.Only (Loc (D (Const ()) (\(Const ()) pt -> Rank2.Only pt)) x)

instance (Differentiable h) => Differentiable (Rank2.Identity h) where
    withLocs (Rank2.Identity x) =
        embedLocs Rank2.Identity (withLocs x)

instance (Differentiable h, Differentiable h') => Differentiable (Rank2.Product h h') where
    withLocs :: forall f. Rank2.Product h h' f 
             -> Rank2.Product h h' (Loc (Rank2.Product h h') f)
    withLocs (Rank2.Pair x y) =
        Rank2.Pair (promoteLeft Rank2.<$> withLocs x)
                   (promoteRight Rank2.<$> withLocs y)
        where
        promoteLeft :: Loc h f a -> Loc (Rank2.Product h h') f a
        promoteLeft (Loc d pt) = 
            Loc (D (Rank2.Pair d y) (\(Rank2.Pair d' y') pt' -> 
                Rank2.Pair (fill d' pt') y')) pt
        promoteRight :: Loc h' f a -> Loc (Rank2.Product h h') f a
        promoteRight (Loc d pt) = 
            Loc (D (Rank2.Pair x d) (\(Rank2.Pair x' d') pt' -> 
                Rank2.Pair x' (fill d' pt'))) pt

instance (Differentiable h, Differentiable h') => Differentiable (Rank2.Sum h h') where
    withLocs (Rank2.InL x) = embedLocs Rank2.InL (withLocs x)
    withLocs (Rank2.InR y) = embedLocs Rank2.InR (withLocs y)

-- Compose requires Rank1 differentiable.



-- Most of the following work is to define the derivative of a derivative,
-- going through the 'HoleRep' representation: `D h x f = h (WithHole x f)`.
data WithHole x f a where
    NotHole :: f a -> WithHole x f a
    Hole :: WithHole x f x

mapWithHole :: (forall y. f y -> g y) -> WithHole x f a -> WithHole x g a
mapWithHole f (NotHole x) = NotHole (f x)
mapWithHole _ Hole = Hole

fillHole :: f x -> WithHole x f y -> f y
fillHole _ (NotHole x) = x
fillHole x Hole = x

newtype HoleRep h x f = HoleRep { getHoleRep :: h (WithHole x f) }

instance (Rank2.Functor h) => Rank2.Functor (HoleRep h x) where
    f <$> HoleRep h = HoleRep (mapWithHole f Rank2.<$> h)

fromHoleRep :: (Rank2.Functor h) => HoleRep h x f -> D h x f
fromHoleRep h = D h (\dh' pt' -> fillHole pt' Rank2.<$> getHoleRep dh')

toHoleRep :: D h x f -> HoleRep h x f
toHoleRep d = HoleRep (fill (NotHole Rank2.<$> d) Hole)

commuteDs :: (Rank2.Functor h) => D (D h x) y f -> D (D h y) x f
commuteDs = mapShapeD fromHoleRep . fromHoleRep . swapHoleReps . toHoleRep . mapShapeD toHoleRep

swapHoleReps :: (Rank2.Functor h) => HoleRep (HoleRep h x) y f -> HoleRep (HoleRep h y) x f
swapHoleReps (HoleRep (HoleRep h)) = HoleRep (HoleRep (swapHoles Rank2.<$> h))
    where
    swapHoles :: WithHole x (WithHole y f) a -> WithHole y (WithHole x f) a
    swapHoles Hole = NotHole Hole
    swapHoles (NotHole Hole) = Hole
    swapHoles (NotHole (NotHole x)) = NotHole (NotHole x)


data HoleRepLoc h f x = HoleRepLoc (HoleRep h x f) (f x)

toHoleRepLoc :: Loc h f x -> HoleRepLoc h f x
toHoleRepLoc (Loc d pt) = HoleRepLoc (toHoleRep d) pt

fromHoleRepLoc :: (Rank2.Functor h) => HoleRepLoc h f x -> Loc h f x
fromHoleRepLoc (HoleRepLoc d pt) = Loc (fromHoleRep d) pt

commuteHoleLoc :: (Rank2.Functor h) => HoleRepLoc h (WithHole x f) y -> WithHole x (HoleRepLoc (HoleRep h x) f) y
commuteHoleLoc (HoleRepLoc d (NotHole fy)) = NotHole (HoleRepLoc (swapHoleReps (HoleRep d)) fy)
commuteHoleLoc (HoleRepLoc _ Hole) = Hole

instance (Differentiable h) => Differentiable (D h x) where
    withLocs = Rank2.fmap (mapShapeLoc fromHoleRep . fromHoleRepLoc)
             . fromHoleRep . HoleRep 
             . Rank2.fmap (commuteHoleLoc . toHoleRepLoc) 
             . withLocs 
             . getHoleRep . toHoleRep

instance (Rank2.Foldable h) => Rank2.Foldable (HoleRep h x) where
    foldMap f = Rank2.foldMap (\case 
        Hole -> mempty
        NotHole x -> f x) . getHoleRep

instance (Rank2.Foldable h) => Rank2.Foldable (D h x) where
    foldMap f = Rank2.foldMap f . toHoleRep

class DFoldable h where
    foldMapD :: (Monoid m, Monoid n) => (forall x. f x -> m) -> (forall x. f x -> n) -> h f -> (m,n)

instance (Rank2.Foldable h) => DFoldable (HoleRep h x) where
    foldMapD f g = 
        (\(_,m,n) -> (m,n))
        . flip appEndo (True,mempty,mempty) -- after starts as True
                                            -- because Endo processes
                                            -- right-to-left (like (.))
        . Rank2.foldMap (\x -> Endo (\(after,m,n) -> 
            case x of
                Hole -> (True,m,n)
                NotHole a
                    | after     -> (after, m, g a <> n)
                    | otherwise -> (after, f a <> m, n)))
        . getHoleRep

instance (Rank2.Foldable h) => DFoldable (D h x) where
    foldMapD f g = foldMapD f g . toHoleRep


sequenceWH :: (Applicative m) => WithHole x (Compose m p) f -> m (WithHole x p f)
sequenceWH Hole = pure Hole
sequenceWH (NotHole x) = NotHole <$> getCompose x

instance (Rank2.Traversable h) => Rank2.Traversable (HoleRep h x) where
    sequence = fmap HoleRep       -- m (HoleRep h x p)
             . Rank2.sequence     -- m (h (WithHole x p))
             . Rank2.fmap comm    -- h (Compose m (WithHole x p))
             . getHoleRep         -- h (WithHole x (Compose m p))
        where
        comm :: (Applicative m) => WithHole x (Compose m p) f -> Compose m (WithHole x p) f
        comm = Compose . sequenceWH 

instance (Rank2.Traversable h) => Rank2.Traversable (D h x) where
    sequence = fmap fromHoleRep . Rank2.sequence . toHoleRep 
