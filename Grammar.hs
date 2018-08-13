{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Grammar where

import Data.Functor.Identity
import Control.Lens (Prism, prism, Prism', prism', makePrisms)

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

-- This does not capture our requirement that a be a product type;
-- or that Shape a f should include information about all cases.
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

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪$≫
infixr 3 ≪|≫

class Grammar g where
    (≪$≫) :: Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    (*≫) :: g () -> g a -> g a
    empty :: g a
    unit :: g ()
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
$( makePrisms ''Defn )

_Nil :: Prism' [a] ()
_Nil = prism' (const []) (\case [] -> Just (); _ -> Nothing)

_Cons :: Prism [a] [b] (a,[a]) (b,[b])
_Cons = prism (uncurry (:)) (\case [] -> Left []; (x:xs) -> Right (x,xs))
-- ^ Is the Left case here correct?


listg :: (Grammar g) => g a -> g [a]
listg g = _Nil ≪$≫ unit
      ≪|≫ _Cons ≪$≫ reg (Tuple2 (g, listg g))

nameg :: (Syntax g) => g Name 
nameg = listg char

expg :: (Syntax g) => g Exp
expg = _Lambda ≪$≫ reg (Tuple2 (nameg, expg))
   ≪|≫ _App ≪$≫ reg (Tuple2 (expg, expg))
   ≪|≫ _Var ≪$≫ nameg
   ≪|≫ _Let ≪$≫ reg (Tuple2 (listg defng, expg))

defng :: (Syntax g) => g Defn
defng = _Defn ≪$≫ reg (Tuple2 (nameg, expg))
