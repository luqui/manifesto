{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies, GADTs, RankNTypes, LambdaCase, ConstraintKinds, DeriveFunctor #-}

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad ((>=>), ap)


data Input i a 
    = Pure a
    | Input (i -> Input i a)
    deriving (Functor)

instance Monad (Input i) where
    return = Pure
    Pure x >>= f = f x
    Input c >>= f = Input (c >=> f)

instance Applicative (Input i) where
    pure = return
    (<*>) = ap

type Command = Char


newtype SemiLens a b = SemiLens { runSemiLens :: a -> Maybe (b, b -> a) }

instance Category SemiLens where
    id = SemiLens $ \x -> Just (x, id)
    SemiLens g . SemiLens f = SemiLens $ \x -> do
        (y,btoa) <- f x
        (z,ctob) <- g y
        return (z, btoa . ctob)

class Node n where
    data Index n :: (* -> *) -> * -> *

    indexLens :: Index n f a -> SemiLens (n f) (f a)


newtype Name = Name String

data Expr f
    = AddExpr (f (Expr f)) (f (Expr f))
    | NegExpr (f (Expr f))
    | VarExpr (f Name)
    | LitExpr (f Integer)


instance Node Expr where
    data Index Expr f t where
        LExprAddLeft :: Index Expr f (Expr f)
        LExprAddRight :: Index Expr f (Expr f)
        LExprNeg :: Index Expr f (Expr f)
        LExprVar :: Index Expr f Name
        LExprLit :: Index Expr f Integer

    indexLens LExprAddLeft = SemiLens $ \case
        AddExpr a b -> Just (a, \a' -> AddExpr a' b)
        _ -> Nothing
    indexLens LExprAddRight = SemiLens $ \case
        AddExpr a b -> Just (b, \b' -> AddExpr a b')
        _ -> Nothing
    indexLens LExprNeg = SemiLens $ \case
        NegExpr a -> Just (a, \a' -> NegExpr a')
        _ -> Nothing
    indexLens LExprVar = SemiLens $ \case
        VarExpr v -> Just (v, \v' -> VarExpr v')
        _ -> Nothing
    indexLens LExprLit = SemiLens $ \case
        LitExpr z -> Just (z, \z' -> LitExpr z')
        _ -> Nothing

