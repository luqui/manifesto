{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.Generics
import Data.Functor.Identity

-- The idea is to transform
--
--    data Tree a = Leaf a | Node (Tree a) (Tree a)
--
-- into
--
--    data TreeF a f = Leaf (f a) | Node (f (Tree a)) (f (Tree a))
--
-- and derive any HFunctor/HFoldable/etc instances.
-- 
-- Notice that we do not descend into the recursive trees.  This is one of the
-- things that makes working with functorized types nice, actually.

data Tree a = Leaf a | Branch (Tree a) (Tree a)
    deriving Generic

instance Shapable (Tree a)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor (Shaped a)) => Shapable a where
    type Shaped a :: (* -> *) -> *
    type Shaped a = ShapedG (Rep a)

    toShape :: a -> Shaped a Identity
    default toShape :: (Generic a, ShapableG (Rep a), Shaped a ~ ShapedG (Rep a)) => a -> Shaped a Identity
    toShape x = toShapeG (from x)
    fromShape :: Shaped a Identity -> a
    default fromShape :: (Generic a, ShapableG (Rep a), Shaped a ~ ShapedG (Rep a)) => Shaped a Identity -> a
    fromShape x = to (fromShapeG x)

class (HFunctor (ShapedG f)) => ShapableG f where
    type ShapedG f :: (* -> *) -> *
    toShapeG :: f p -> ShapedG f Identity
    fromShapeG :: ShapedG f Identity -> f p

newtype Field a f = Field { getField :: f a }
    deriving (Generic)

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance ShapableG (K1 i t) where
    type ShapedG (K1 i t) = Field t
    toShapeG = Field . Identity . unK1
    fromShapeG = K1 . runIdentity . getField

instance (ShapableG f) => ShapableG (M1 i c f) where
    type ShapedG (M1 i c f) = ShapedG f
    toShapeG = toShapeG . unM1
    fromShapeG = M1 . fromShapeG

-- We reuse :+: and :*: in the codomain, since they are exactly what we need
instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
    hfmap f (L1 x) = L1 (hfmap f x)
    hfmap f (R1 y) = R1 (hfmap f y)

instance (ShapableG f, ShapableG g) => ShapableG (f :+: g) where
    type ShapedG (f :+: g) = ShapedG f :+: ShapedG g
    toShapeG (L1 x) = L1 (toShapeG x)
    toShapeG (R1 y) = R1 (toShapeG y)
    fromShapeG (L1 x) = L1 (fromShapeG x)
    fromShapeG (R1 y) = R1 (fromShapeG y)

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
    hfmap f (x :*: y) = hfmap f x :*: hfmap f y

instance (ShapableG f, ShapableG g) => ShapableG (f :*: g) where
    type ShapedG (f :*: g) = ShapedG f :*: ShapedG g 
    toShapeG (x :*: y) = toShapeG x :*: toShapeG y
    fromShapeG (x :*: y) = fromShapeG x :*: fromShapeG y
