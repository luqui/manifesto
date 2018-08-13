{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Grammar where

import qualified Control.Lens as L
import Monoidal
import Control.Applicative (liftA2, (<|>))
import Control.Monad ((<=<))
import Data.Kind (Constraint)

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class (Monoidal g) => Grammar g where
    (≪?≫) :: L.Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

class (Grammar g) => Syntax g where
    type SyContext g :: * -> Constraint
    char :: g Char
    focus :: (SyContext g a) => g a -> g a


data Hole c a where
    Hole :: c b => b -> (b -> a) -> Hole c a

instance (Show a) => Show (Hole Show a) where
    show (Hole b _) = "Hole(" ++ show b ++ ")"

instance Functor (Hole c) where
    fmap f (Hole b c) = Hole b (f . c)

idHole :: (c a) => a -> Hole c a
idHole x = Hole x id

instance IsoFunctor (Hole c) where
    isomap = L.mapping

data Context c a = Context a [Hole c a]

deriving instance (Show a) => Show (Context Show a)

instance Functor (Context c) where
    fmap f (Context x xhs) = Context (f x) ((map.fmap) f xhs)

$( L.makePrisms ''Context )

instance IsoFunctor (Context c) where
    isomap = L.mapping

instance Monoidal (Context c) where
    unit = Context () []
    Context x xhs ≪*≫ Context y yhs
        = Context (x,y) ((fmap.fmap) (,y) xhs ++ (fmap.fmap) (x,) yhs)

addFocus :: (c a) => Context c a -> Context c a 
addFocus (Context x xhs) = Context x (idHole x : xhs)

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

instance Syntax (Editor c) where
    type SyContext (Editor c) = c
    char = Editor (\c -> pure (Context c []))
    focus = Editor . (fmap.fmap) addFocus . runEditor

-- Say we have a grammar like this
type Name = String

data Exp
    = Lambda Name Exp
    | App Exp Exp
    | Var Name
    | Let [Defn] Exp
    deriving (Show)

data Defn
    = Defn Name Exp
    deriving (Show)

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

expg :: (Syntax g, SyContext g Exp, SyContext g Defn) => g Exp
expg = focus $
       _Lambda ≪?≫ nameg ≪:≫ expg
   ≪|≫ _App ≪?≫ expg ≪:≫ expg
   ≪|≫ _Var ≪?≫ nameg
   ≪|≫ _Let ≪?≫ listg defng ≪:≫ expg

defng :: (Syntax g, SyContext g Defn, SyContext g Exp) => g Defn
defng = focus $ _Defn ≪?≫ nameg ≪:≫ expg
