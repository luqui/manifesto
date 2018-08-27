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

-- Let's say we have an normal expression type like this

newtype Name = Name String

data Defn
    = Defn Name Exp

data Exp
    = ELambda Name Exp
    | EApp Exp Exp
    | EVar Name
    | ELet [Defn] Exp

type Program = [Defn]

-- We want to be able to pull each of these apart, in such a way that we can
-- construct a context frame and "see" the types of subexpressions.

-- In particular, we have to have a type-changing context; e.g. when ELet_1 is
-- on the context stack, the next level down will be a list context, and the
-- next a Defn context.

data Loc h f a = Loc (D h f a) (f a)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor h) => Differentiable h where
    data D h :: (* -> *) -> * -> *
    toFrames :: h f -> h (Loc h f)
    fillHole :: Loc h f a -> h f

class (HFunctor h) => Serial h where
    constToList :: h (Const b) -> [b]



newtype Field a f = Field { getField :: f a }

instance HFunctor (Field a) where
    hfmap f (Field x) = Field (f x)

instance Serial (Field a) where
    constToList (Field (Const a)) = [a]

instance Differentiable (Field a) where
    data D (Field a) f x where
        DField :: D (Field a) f a
    toFrames (Field x) = Field (Loc DField x)
    fillHole (Loc DField x) = Field x


newtype Const a f = Const { getConst :: a }

instance HFunctor (Const a) where
    hfmap _ (Const x) = Const x

instance Differentiable (Const a) where
    data D (Const a) f x
    toFrames (Const x) = Const x
    fillHole (Loc cx _) = case cx of {}

instance Serial (Const a) where
    constToList (Const _) = []


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

instance (Serial h, Serial h') => Serial (h :*: h') where
    constToList (HPair a b) = constToList a ++ constToList b

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

instance (Serial h, Serial h') => Serial (h :+: h') where
    constToList (HLeft a) = constToList a
    constToList (HRight b) = constToList b

{-

-- All boilerplate.
instance Node Defn where
    data Frame Defn t where
        DefnF1 :: Exp -> Frame Defn Name
        DefnF2 :: Name -> Frame Defn Exp
    data Base Defn f where
        DefnB :: f Name -> f Exp -> Base Defn f

    toBase (Defn n e) = DefnB (Identity n) (Identity e)
    fromBase (DefnB (Identity n) (Identity e)) = Defn n e
    toFrames (Defn n e) = DefnB (Loc (DefnF1 e) n) (Loc (DefnF2 n) e)
    fillHole (Loc (DefnF1 e) n) = Defn n e
    fillHole (Loc (DefnF2 n) e) = Defn n e

instance HFunctor (Base Defn) where
    hfmap f (DefnB n e) = DefnB (f n) (f e)

instance Node () where
    data Frame () t where
    data Base () f where
        UnitB :: Base () f

    toBase () = UnitB
    fromBase UnitB = ()
    toFrames () = UnitB
    fillHole (Loc cx _) = case cx of {}
    
instance HFunctor (Base ()) where
    hfmap _ UnitB = UnitB

instance Node (Maybe a) where
    data Frame (Maybe a) t where
        JustF :: Frame (Maybe a) a
    data Base (Maybe a) f where
        MaybeB :: Maybe (f a) -> Base (Maybe a) f

    toBase m = MaybeB (Identity <$> m)
    fromBase (MaybeB m) = runIdentity <$> m
    toFrames Nothing = MaybeB Nothing
    toFrames (Just x) = MaybeB (Just (Loc JustF x))
    fillHole (Loc JustF x) = Just x

instance HFunctor (Base (Maybe a)) where
    hfmap f (MaybeB m) = MaybeB (fmap f m)


instance Node [a] where
    data Frame [a] t where
        ListF :: [a] -> [a] -> Frame [a] a
    data Base [a] f where
        ListB :: [f a] -> Base [a] f

    toBase xs = ListB (map Identity xs)
    fromBase (ListB xs) = map runIdentity xs
    toFrames xs = ListB $ do
        (pre, x:post) <- zip (tails (reverse xs)) (tails xs) 
        return $ Loc (ListF pre post) x
    fillHole (Loc (ListF pre post) x) = reverse pre ++ [x] ++ post

instance HFunctor (Base [a]) where
    hfmap f (ListB xs) = ListB (map f xs)


-}
