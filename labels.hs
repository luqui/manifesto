{-# LANGUAGE PolyKinds, DataKinds, GADTs #-}

import Data.Kind (Type)

-- Same modeling power as Label = f Identity
data L = Label ((L -> Type) -> Type)

data Expr f = 
    Add (f (Label Expr)) (f (Label Expr))

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

