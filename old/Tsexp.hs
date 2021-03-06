{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Control.Arrow (first)
import Data.Functor.Const (Const(..))
import Data.Monoid (Dual(..))
import Data.Functor.Compose (Compose(..))

import qualified Rank2
import Data.Functor.Differentiable.Rank2

type Serial h = (Differentiable h, Rank2.Foldable h)

-- This is a higher-kinded version of an F-algebra, of sorts.  It takes
-- the observations of the children into the observations of the parent.
type Alg h f s = h f -> f s

data Tsexp f s where
    Tsexp :: (Serial h) => Alg h f s -> h (Tsexp f) -> Tsexp f s
-- The first argument here is the "algebra", and it is (in principle)
-- associated with the shape alone -- the "data" of the node is all in the
-- second argument.

data Context1 f a b  where
    Context1 :: (Serial h) => Alg h f a -> D h b (Tsexp f) -> Context1 f a b

data Context f a b where
    CNil  :: Context f a a
    CCons :: Context f a b -> Context1 f b c -> Context f a c

data Zipper f a where
    Zipper :: Context f a b -> Tsexp f b -> Zipper f a

newZipper :: Tsexp f s -> Zipper f s
newZipper = Zipper CNil

fillContext1 :: Context1 f s s' -> Tsexp f s' -> Tsexp f s
fillContext1 (Context1 alg d) e = Tsexp alg (fromLoc (Loc d e))

zipUpContext :: Context f a b -> Tsexp f b -> Tsexp f a
zipUpContext CNil = id
zipUpContext (CCons cx cx1) = zipUpContext cx . fillContext1 cx1

zipUp :: Zipper f a -> Tsexp f a
zipUp (Zipper cx e) = zipUpContext cx e

up :: Zipper f a -> Maybe (Zipper f a)
up (Zipper CNil _) = Nothing
up (Zipper (CCons cx cx1) e) = Just (Zipper cx (fillContext1 cx1 e))

down :: Zipper f a -> [Zipper f a]
down (Zipper cx (Tsexp alg dat)) = 
    Rank2.foldMap ((:[]) . getConst) $
        Rank2.fmap (\(Loc d e) -> Const (Zipper (CCons cx (Context1 alg d)) e)) 
                   (withLocs dat)

siblings :: Zipper f a -> ([Zipper f a], [Zipper f a])
siblings (Zipper CNil _) = ([], [])
siblings (Zipper (CCons cx (Context1 alg d)) e) 
    = first getDual . foldMapD (Dual . (:[]) . getConst) ((:[]) . getConst) $ 
        Rank2.fmap (\loc -> Const (Zipper (CCons cx (Context1 alg (fromLoc loc))) e))
                   (withLocs d)

synthesize :: Tsexp f s -> f s
synthesize (Tsexp alg dat) = alg (synthesize Rank2.<$> dat)

-- Using a way that one of the observations f supports gives another Exp, we
-- can edit the zipper at the current point using that observation.
editZ :: (Functor g) => (forall s. f s -> g (Tsexp f s)) -> Zipper f a -> g (Zipper f a)
editZ observe (Zipper cx e) = Zipper cx <$> observe (synthesize e)


-- Basic
data Expr 
    = Add Expr Expr
    | Lit Integer

data Obs s = Obs {
    value :: s,
    pretty :: String,
    -- An example rewrite
    modLit :: Maybe (Integer -> Tsexp Obs s)
  }

-- Plug this into editZ
observeModLit :: Obs s -> Compose Maybe ((->) Integer) (Tsexp Obs s)
observeModLit = Compose . modLit

toTsexp :: Expr -> Tsexp Obs Integer
toTsexp (Add x y) = 
    Tsexp (\(Rank2.Pair (Rank2.Only x') (Rank2.Only y')) -> 
        Obs { value = value x' + value y'
            , pretty = "(" ++ pretty x' ++ "+" ++ pretty y' ++ ")"
            , modLit = Nothing 
            }) 
        (Rank2.Pair (Rank2.Only (toTsexp x)) (Rank2.Only (toTsexp y)))
toTsexp (Lit z) = Tsexp (\(Rank2.Only obs) -> 
        Obs { value = value obs
            , pretty = pretty obs
            , modLit = Nothing 
            }) 
        (Rank2.Only (toTsexpInt z))

toTsexpInt :: Integer -> Tsexp Obs Integer
toTsexpInt z = Tsexp obs (Const z)
    where
    obs :: Const Integer Obs -> Obs Integer
    obs (Const z') = Obs { value = z'
                         , pretty = show z'
                         , modLit = Just toTsexpInt
                         }

exampleExp :: Expr
exampleExp = Add (Lit 1) (Add (Lit 2) (Lit 3))

main :: IO ()
main = do
    let z = newZipper (toTsexp exampleExp)
    putStrLn $ pretty (synthesize (zipUp z)) ++ " = " ++ show (value (synthesize (zipUp z)))
    [z',_] <- return $ down z
    ([], [_]) <- return $ siblings z'  -- just proof that siblings works
    [z''] <- return $ down z'
    Just f <- return . getCompose $ editZ observeModLit z''
    let z''' = f 10 
    putStrLn $ pretty (synthesize (zipUp z''')) ++ " = " ++ show (value (synthesize (zipUp z''')))
