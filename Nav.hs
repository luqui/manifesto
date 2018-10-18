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
import           Data.Monoid (First(..))

type IsNode h = (D.Differentiable h, Rank2.Foldable h)

data Tree g l where
    Tree :: (Locus h g, IsNode h) => h (Tree g) -> Tree g (L h)

-- Each level of the context stores the grammar associated with that level.
data Context g l h where
    CxNil :: g h -> Context g (L h) h
    CxCons :: (Locus h g, IsNode h) => Context g l h -> g h' -> D.D h (L h') (Tree g) -> Context g l h'

getContext :: Context g l h -> g h
getContext (CxNil g) = g
getContext (CxCons _ g _) = g

data Zipper g l where
    Zipper :: Context g l h -> Tree g (L h) -> Zipper g l

down :: (Closed g) => Zipper g l -> [Zipper g l]
down (Zipper cx (Tree h)) = Rank2.foldMap (\(Pair loc (OnLabel g)) -> [Zipper (CxCons cx g (D.context loc)) (D.focus loc)]) 
                                          (fromFirst (closed (getContext cx) (D.withLocs h)))
    where
    fromFirst (First (Just x)) = x
    fromFirst _ = error "Incomplete grammar"  -- There is probably a missing case in a chain of ≪|≫s.

up :: Zipper g l -> Maybe (Zipper g l)
up (Zipper (CxNil _) _) = Nothing
up (Zipper (CxCons cx _ d) t) = Just (Zipper cx (Tree (D.fill d t)))


