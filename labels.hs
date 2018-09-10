{-# LANGUAGE PolyKinds, DataKinds, GADTs, TypeFamilies, TypeOperators, RankNTypes, KindSignatures, FlexibleContexts #-}

import Data.Kind (Type)

-- Same modeling power as Label = f Identity
data L = Label ((L -> Type) -> Type)

data Expr f = 
    Add (f (Label Expr)) (f (Label Expr))


-- Here's one way to tie the knot.
-- Promote takes a shape functor into a label-indexed
-- functor, i.e. (k -> *) -> (k -> *) ...
data Promote l f a where 
    Promote :: h f -> Promote l f (l h)

-- ... which has a fix-able kind.  (N.B. make a class for Mu to kind-generically roll and unroll)
data family Mu :: (k -> k) -> k
data instance Mu f = Mu1 (f (Mu f))
data instance Mu f a = Mu2 (f (Mu f) a)

-- Oh look, a little exposition in kind-categories.  Maybe this idea has more
-- clout than I once believed.
data family (~>) :: k -> k -> *
data instance (~>) a b = Fun1 (a -> b)
data instance (~>) a b = Fun2 (forall x. a x -> b x)

data OrdCat = OrdCat Type
type family GetOrd c where
    GetOrd ('OrdCat t) = t
data instance (~>) a b = FunOrd ((Ord (GetOrd a), Ord (GetOrd b)) => GetOrd a -> GetOrd b)

class Fixpoint k where
    roll :: forall (f :: k -> k). f (Mu f) ~> Mu f
    unroll :: forall (f :: k -> k). Mu f ~> f (Mu f)

-- Note how Mu2 (Promote Label) is totally independent of Expr, it is a
-- "generic" recurser.   We could, for example, build a generic zipper for
-- this.
type ExprTied = Mu (Promote Label) (Label Expr)


-- We can do type-annotated syntax with this scheme too (as I believe we could
-- with f Identity)
data TExpr t f where
    Add' :: f (Label (TExpr Int)) -> f (Label (TExpr Int)) -> TExpr Int f
    Show' :: f (Label (TExpr Int)) -> TExpr String f


-- And we can do more too, if we use polymorphic labels.  I don't know
-- what the use of this is, exactly...
data L' = Label' (Type -> (L' -> Type) -> Type)

data Foo t f where
    Fao :: f (Label' Foo) -> Foo Int f


-- We can parameterize over the label constructor.  (Why tho?)
data Literal a l f = Literal a

data Bar l f = Bar (f (l (Bar l))) (f (l (Literal Bool l)))


-- I guess one thing you can do with labels is have labels that don't embed a constructor,
-- or embed multiple. 

data M = Mabel ((M -> Type) -> Type)
       | Mabel2 ((M -> Type) -> Type) ((M -> Type) -> Type)
       | Lit Type
       | Ann

data Baz f = Baz (f (Lit Bool)) (f Ann) (f (Mabel Baz))
           | Baz2 (f (Mabel2 Baz Baz))

-- Here's how we use the parametrically labeled Bar to embed a Bar into 
-- a more sophisticated label class.
type BarM = Bar 'Mabel

-- Seems like there is a lot of power here.  I don't know how to use it yet.
