{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Grammar where

import Data.Functor.Identity
import Control.Lens (Prism', makePrisms)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

class (HFunctor (Shape a)) => Regular a where
    data Shape a :: (* -> *) -> *

    toShape :: a -> Shape a Identity
    fromShape :: Shape a Identity -> a

instance Regular (a,b) where
    newtype Shape (a,b) f
        = Tuple2 (f a, f b)
    toShape (a,b) = Tuple2 (Identity a, Identity b)
    fromShape (Tuple2 (Identity a, Identity b)) = (a,b)

instance HFunctor (Shape (a,b)) where
    hfmap f (Tuple2 (a, b)) = Tuple2 (f a, f b)

-- Wrong from our perspective.
-- Regular should define a *covering*, not just an instance
instance Regular [a] where
    newtype Shape [a] f
        = List [f a]
    toShape xs = List (map Identity xs)
    fromShape (List xs) = map runIdentity xs

instance HFunctor (Shape [a]) where
    hfmap f (List xs) = List (map f xs)

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪$≫
infixr 3 ≪|≫

class Grammar g where
    (≪$≫) :: Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    (*≫) :: g () -> g a -> g a
    empty :: g a
    reg :: (Regular a) => Shape a g -> g a

class (Grammar g) => Syntax g where
    char :: g Char

-- Say we have a grammar like this
type Name = String

data Exp
    = Lambda Name Exp
    | App Exp Exp
    | Var Name
    | Let [Defn] Exp

data Defn
    = Defn Name Exp

$( makePrisms ''Exp )

-- wrong
nameg :: (Syntax g) => g Name 
nameg = reg (List [char])

expg :: (Syntax g) => g Exp
expg = _Lambda ≪$≫ reg (Tuple2 (nameg, expg))
   ≪|≫ _App ≪$≫ reg (Tuple2 (expg, expg))
   ≪|≫ _Var ≪$≫ nameg
-- ≪|≫ _Let ≪$≫ reg (Tuple2 (defnsg, expg))

