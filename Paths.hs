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


newtype SemiLens a b = SemiLens { runSemiLens :: a -> Maybe (b, b -> a) }

instance Category SemiLens where
    id = SemiLens $ \x -> Just (x, id)
    SemiLens g . SemiLens f = SemiLens $ \x -> do
        (y,btoa) <- f x
        (z,ctob) <- g y
        return (z, btoa . ctob)


class Node a where
    data Link a :: * -> *

    linkLens :: Link a b -> SemiLens a b
    

data Path a b where
    PNil :: Path a a
    PLink :: (Node b) => Path a b -> Link b c -> Path a c

pathLens :: Path a b -> SemiLens a b
pathLens PNil = id
pathLens (PLink p l) = linkLens l . pathLens p

data Located a b = Located a (Path a b)

data Ex c f where
    Ex :: (c a) => f a -> Ex c f

newtype Editor a = Editor { runEditor :: forall b. (Node b) => Located a b -> Ex Node (Located a) }


newtype Name = Name String

data Program 
    = Program [Defn]

instance Node Program where
    data Link Program t where 
        LProgram :: Int -> Link Program Defn

    linkLens (LProgram n) = SemiLens $ \case
        Program defns
            | 0 < n && n < length defns -> Just (defns !! n, \defn' -> Program (take n defns ++ [defn'] ++ drop (n+1) defns))
            | otherwise -> Nothing


data Defn
    = Defn Name Expr

instance Node Defn where
    data Link Defn t where
        LDefnName :: Link Defn Name
        LDefnExpr :: Link Defn Expr

    linkLens LDefnName = SemiLens $ \case
        Defn name expr -> Just (name, \name' -> Defn name' expr)
    linkLens LDefnExpr = SemiLens $ \case
        Defn name expr -> Just (expr, \expr' -> Defn name expr')


data Expr
    = AddExpr Expr Expr
    | NegExpr Expr
    | VarExpr Name
    | LitExpr Integer


instance Node Expr where
    data Link Expr t where
        LExprAddLeft :: Link Expr Expr
        LExprAddRight :: Link Expr Expr
        LExprNeg :: Link Expr Expr
        LExprVar :: Link Expr Name
        LExprLit :: Link Expr Integer

    linkLens LExprAddLeft = SemiLens $ \case
        AddExpr a b -> Just (a, \a' -> AddExpr a' b)
        _ -> Nothing
    linkLens LExprAddRight = SemiLens $ \case
        AddExpr a b -> Just (b, \b' -> AddExpr a b')
        _ -> Nothing
    linkLens LExprNeg = SemiLens $ \case
        NegExpr a -> Just (a, \a' -> NegExpr a')
        _ -> Nothing
    linkLens LExprVar = SemiLens $ \case
        VarExpr v -> Just (v, \v' -> VarExpr v')
        _ -> Nothing
    linkLens LExprLit = SemiLens $ \case
        LitExpr z -> Just (z, \z' -> LitExpr z')
        _ -> Nothing

