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
import Control.Applicative (liftA2, (<|>))
import Control.Monad ((<=<))

import Monoidal

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class (Monoidal g) => Grammar g where
    (≪?≫) :: L.Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

class (Grammar g) => Syntax g where
    type HoleData g :: * -> *
    char :: g Char
    focus :: (a -> HoleData g a) -> g a -> g a


data Context f a = Context a [f a]

addFocus :: (a -> f a) -> Context f a -> Context f a
addFocus f (Context x xhs) = Context x (f x : xhs)

instance (Functor f) => Functor (Context f) where
    fmap f (Context x xhs) = Context (f x) ((map.fmap) f xhs)

$( L.makePrisms ''Context )

instance (Functor f) => IsoFunctor (Context f) where
    isomap = L.mapping

instance (Functor f) => Monoidal (Context f) where
    unit = Context () []
    Context x xhs ≪*≫ Context y yhs
        = Context (x,y) ((fmap.fmap) (,y) xhs ++ (fmap.fmap) (x,) yhs)

newtype Editor f a = Editor { runEditor :: a -> Maybe (Context f a) }

$( L.makePrisms ''Editor )

instance (Functor f) => IsoFunctor (Editor f) where
    isomap i = _Editor . L.dimapping (L.from i) (L.mapping (isomap i)) . L.from _Editor

instance (Functor f) => Monoidal (Editor f) where
    unit = Editor (\() -> pure unit)
    Editor f ≪*≫ Editor g = Editor $ \(x,y) -> liftA2 (≪*≫) (f x) (g y)

instance (Functor f) => Grammar (Editor f) where
    empty = Editor (\_ -> Nothing)
    p ≪?≫ ed = Editor $ (fmap.fmap) (L.review p) . runEditor ed <=< L.preview p
    ed ≪|≫ ed' = Editor $ \x -> runEditor ed x <|> runEditor ed' x

instance (Functor f) => Syntax (Editor f) where
    type HoleData (Editor f) = f
    char = Editor (\c -> pure (Context c []))
    focus p = Editor . (fmap.fmap) (addFocus p) . runEditor

-- Say we have a grammar like this
type Name = String

data Exp
    = Lambda Name Exp
    | App Exp Exp
    | Var Name
    | Let [Defn] Exp
    deriving (Read, Show)

data Defn
    = Defn Name Exp
    deriving (Read, Show)

$( L.makePrisms ''Exp )
$( L.makePrisms ''Defn )

_Nil :: L.Prism' [a] ()
_Nil = L.prism' (const []) (\case [] -> Just (); _ -> Nothing)

_Cons :: L.Prism [a] [b] (a,[a]) (b,[b])
_Cons = L.prism (uncurry (:)) (\case [] -> Left []; (x:xs) -> Right (x,xs))


reread :: (Read a, Show a) => a -> IO a
reread x = do
    putStrLn $ "Was: " ++ show x
    putStr "Now? "
    readLn
    


listg :: (Grammar g) => g a -> g [a]
listg g = _Nil ≪?≫ unit
      ≪|≫ _Cons ≪?≫ g ≪:≫ listg g

nameg :: (Syntax g) => g Name 
nameg = listg char

expg :: (Syntax g, HoleData g ~ IO) => g Exp
expg = focus reread $
       _Lambda ≪?≫ nameg ≪:≫ expg
   ≪|≫ _App ≪?≫ expg ≪:≫ expg
   ≪|≫ _Var ≪?≫ nameg
   ≪|≫ _Let ≪?≫ listg defng ≪:≫ expg

defng :: (Syntax g, HoleData g ~ IO) => g Defn
defng = focus reread $ _Defn ≪?≫ nameg ≪:≫ expg


main :: IO ()
main = do
    case runEditor expg (App (Var "foo") (Var "bar")) of
        Just (Context _ [_, hio, _]) ->
            print =<< hio
        _ -> putStrLn "Bullshit"
