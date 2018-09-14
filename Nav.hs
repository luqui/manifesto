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

import           Data.Constraint ((:-)(..), Dict(..))
import qualified Data.Functor.Differentiable.Rank2 as D
import           Data.Proxy (Proxy(..))
import           Grammar
import qualified Rank2

data Annotated f l where
    Annotated :: (Semantics f h) 
              => f (L h) -> h (Annotated f) -> Annotated f (L h)

instance (Semantics f h) => Semantics (Annotated f) h where
    sem hann = Annotated (sem hf) hann
        where
        hf = Rank2.fmap (\(Annotated fa _) -> fa) hann

newtype c := c' = Sub2 (forall x. c x :- c' x)

class NavF f where
    isFoldable :: f (L h) -> Dict (Rank2.Foldable h)
    isDifferentiable :: f (L h) -> Dict (D.Differentiable h)

mapAnnotated :: SemMorph f f' -> (forall x. f x -> f' x) -> Annotated f x -> Annotated f' x
mapAnnotated m f (Annotated c h) = morphSem (hproxy h) m (Annotated (f c) (Rank2.fmap (mapAnnotated m f) h))
    where
    hproxy :: h a -> Proxy h
    hproxy _ = Proxy


data Context f h l where
    CTop :: Context f (Only l) l
    CCons :: (Semantics f h') => Context f h (L h') -> D.D h' l (Annotated f) -> Context f h l

data Zipper f h where
    Zipper :: Context f h l -> Annotated f l -> Zipper f h

up :: Zipper f h -> Maybe (Zipper f h)
up (Zipper CTop _) = Nothing
up (Zipper (CCons cx d) t@Annotated{}) = Just (Zipper cx (sem (D.fill d t)))

down :: NavF f => Zipper f h -> [Zipper f h]
down (Zipper cx (Annotated f h)) 
    | Dict <- isFoldable f
    , Dict <- isDifferentiable f
    = Rank2.foldMap (\(D.Loc d x) -> [Zipper (CCons cx d) x]) (D.withLocs h)
