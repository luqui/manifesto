{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Grammar where

import qualified Control.Lens as L
import Monoidal
import Control.Applicative (liftA2, (<|>))
import Control.Monad ((<=<))

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class (Monoidal g) => Grammar g where
    (≪?≫) :: L.Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

class (Grammar g) => Syntax g where
    char :: g Char


data Hole c a where
    Hole :: c b => b -> (b -> a) -> Hole c a

instance Functor (Hole c) where
    fmap f (Hole b c) = Hole b (f . c)

extract :: Hole c a -> a
extract (Hole x f) = f x

instance IsoFunctor (Hole c) where
    isomap = L.mapping

data Context c a = Context a [Hole c a]

instance Functor (Context c) where
    fmap f (Context x xhs) = Context (f x) ((map.fmap) f xhs)

$( L.makePrisms ''Context )

instance IsoFunctor (Context c) where
    isomap = L.mapping

instance Monoidal (Context c) where
    unit = Context () []
    Context x xhs ≪*≫ Context y yhs
        = Context (x,y) ((fmap.fmap) (,y) xhs ++ (fmap.fmap) (x,) yhs)


newtype Editor c a = Editor { runEditor :: a -> Maybe (Context c a) }

$( L.makePrisms ''Editor )

instance IsoFunctor (Editor c) where
    isomap i = _Editor . L.dimapping (L.from i) (L.mapping (isomap i)) . L.from _Editor

instance Monoidal (Editor c) where
    unit = Editor (\() -> pure unit)
    Editor f ≪*≫ Editor g = Editor $ \(x,y) -> liftA2 (≪*≫) (f x) (g y)

instance Grammar (Editor c) where
    empty = Editor (\_ -> Nothing)
    p ≪?≫ ed = Editor $ (fmap.fmap) (L.review p) . runEditor ed <=< L.preview p
    ed ≪|≫ ed' = Editor $ \x -> runEditor ed x <|> runEditor ed' x


-- Say we have a grammar like this
type Name = String

data Exp
    = Lambda Name Exp
    | App Exp Exp
    | Var Name
    | Let [Defn] Exp

data Defn
    = Defn Name Exp

$( L.makePrisms ''Exp )
$( L.makePrisms ''Defn )

_Nil :: L.Prism' [a] ()
_Nil = L.prism' (const []) (\case [] -> Just (); _ -> Nothing)

_Cons :: L.Prism [a] [b] (a,[a]) (b,[b])
_Cons = L.prism (uncurry (:)) (\case [] -> Left []; (x:xs) -> Right (x,xs))


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
