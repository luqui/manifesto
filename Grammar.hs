{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Grammar where

import Control.Lens (Prism, prism, Prism', prism', makePrisms)
import Monoidal

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class (Monoidal g) => Grammar g where
    (≪?≫) :: Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

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
listg g = _Nil ≪?≫ unit
      ≪|≫ _Cons ≪?≫ g ≪:≫ listg g

nameg :: (Syntax g) => g Name 
nameg = listg char

expg :: (Syntax g) => g Exp
expg = _Lambda ≪?≫ nameg ≪:≫ expg
   ≪|≫ _App ≪?≫ expg ≪:≫ expg
   ≪|≫ _Var ≪?≫ nameg
   ≪|≫ _Let ≪?≫ listg defng ≪:≫ expg

defng :: (Syntax g) => g Defn
defng = _Defn ≪?≫ nameg ≪:≫ expg
