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

import           Data.Bifunctor (first)
import           Data.Constraint ((:-)(..), Dict(..))
import qualified Data.Functor.Differentiable.Rank2 as D
import           Data.Monoid (First(..), Dual(..))
import           Data.Proxy (Proxy(..))
import           Grammar
import qualified Rank2




-- Assumptions required for navigating.
type NavAssumptions f h = (Rank2.Foldable h, D.Differentiable h, Locus h f)

-- Fortunately they can be derived from the grammar.
data NavAssumptionsSem f h where
    NavAssumptionsSem :: NavAssumptions f h => NavAssumptionsSem f h

instance Grammar (NavAssumptionsSem f) where
    _ ≪?≫ NavAssumptionsSem = NavAssumptionsSem

instance (NavAssumptions f g) => Locus g (NavAssumptionsSem f) where
    locus _ = NavAssumptionsSem


class Navable f where
    navAssumptions :: f h -> Dict (NavAssumptions f h)

mapAnnotated :: (Navable f) => (forall x. f x -> f' x) -> Annotated f x -> Annotated f' x
mapAnnotated f (Annotated c h)
    | Dict <- navAssumptions c
    = Annotated (f c) (Rank2.fmap (mapAnnotated f) h)

{-
data DAnnotated f h l = DAnnotated (f (L h)) (D.D h l (Annotated f))
                                 -- ^ Should be a D f, once we have rank 1 derivatives. 

dAnnNavAssumptions :: (Navable f) => DAnnotated f h l -> Dict (NavAssumptions f h)
dAnnNavAssumptions (DAnnotated f _) = navAssumptions f

fillDAnn :: (Navable f) => DAnnotated f h l -> Annotated f l -> Annotated f (L h)
fillDAnn (DAnnotated f d) ann 
    | Dict <- navAssumptions f
    = sem (D.fill d ann)

data Context f h l where
    CTop :: Context f (Only l) l
    CCons :: Context f h (L h') -> DAnnotated f h' l -> Context f h l

data Zipper f h where
    Zipper :: Context f h l -> Annotated f l -> Zipper f h

up :: (Navable f) => Zipper f h -> Maybe (Zipper f h)
up (Zipper CTop _) = Nothing
up (Zipper (CCons cx d) t) = Just (Zipper cx (fillDAnn d t))

down :: (Navable f) => Zipper f h -> [Zipper f h]
down (Zipper cx (Annotated f h)) 
    | Dict <- navAssumptions f
    = Rank2.foldMap (\(D.Loc d x) -> [Zipper (CCons cx (DAnnotated f d)) x]) (D.withLocs h)

siblings :: (Navable f) => Zipper f h -> ([Zipper f h], [Zipper f h])
siblings (Zipper CTop _) = ([],[])
siblings (Zipper (CCons cx d@(DAnnotated f d')) t) 
    | Dict <- dAnnNavAssumptions d
    = first getDual . D.foldMapD (Dual . pure . getConst) (pure . getConst) $ 
        Rank2.fmap (\(D.Loc dd t')  -> 
            let dann = DAnnotated f (D.fill (D.commuteDs dd) t) in
            Const (Zipper (CCons cx dann) t')
        )
        (D.withLocs d')
-}
