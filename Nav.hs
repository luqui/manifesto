{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Nav where

import           Grammar hiding (Tree)
import qualified Rank2
import qualified Data.Functor.Differentiable.Rank2 as D

type IsNode h = (D.Differentiable h, Rank2.Foldable h)

data Tree g l where
    Tree :: (Locus h g, IsNode h) => h (Tree g) -> Tree g (L h)

data Context g l l' where
    CxNil :: Context g l l
    CxCons :: (Locus h g, IsNode h) => Context g l (L h) -> D.D h l' (Tree g) -> Context g l l'

data Zipper g l where
    Zipper :: Context g l l' -> Tree g l' -> Zipper g l

down :: Zipper g l -> [Zipper g l]
down (Zipper cx (Tree h)) = Rank2.foldMap (\loc -> [Zipper (CxCons cx (D.context loc)) (D.focus loc)]) (D.withLocs h)

up :: Zipper g l -> Maybe (Zipper g l)
up (Zipper CxNil _) = Nothing
up (Zipper (CxCons cx d) t) = Just (Zipper cx (Tree (D.fill d t)))


