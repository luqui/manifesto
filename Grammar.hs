{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
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
{-# LANGUAGE TypeOperators #-}

module Grammar where

import qualified Control.Lens as L
import Control.Applicative (liftA2, (<|>))
import Control.Monad ((<=<))

import Data.Functor.Identity
import Data.Functor.Const
import Monoidal

-- ... Looks a lot like a bidirectional applicative/alternative.
infix 4 ≪?≫
infixr 3 ≪|≫

class HFunctor h where
    hfmap :: (forall x. f x -> g x) -> h f -> h g

instance HFunctor (Const b) where
    hfmap _ (Const x) = Const x

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
    hfmap f (Product x y) = Product (hfmap f x) (hfmap f y)

class (Monoidal g) => Grammar g where
    (≪?≫) :: L.Prism' a b -> g b -> g a
    (≪|≫) :: g a -> g a -> g a
    empty :: g a

class (Grammar g) => Syntax g where
    type SyntaxF g :: * -> *
    char :: g Char
    focus :: (SyntaxF g a -> SyntaxF g a) -> g a -> g a

data PolySExp op a where
    PolySExp :: (HFunctor f) => op f -> (f Identity -> a) -> f (PolySExp op) -> PolySExp op a

extract :: PolySExp op a -> a
extract = runIdentity . go
    where
    go :: PolySExp op a -> Identity a
    go (PolySExp _ recon children) = Identity (recon (hfmap go children))

class HMonoidal op where
    hunit :: op (Const ())
    hprod :: op f -> op g -> op (f :*: g)

deriving instance Functor (PolySExp op)
instance IsoFunctor (PolySExp op)
instance (HMonoidal op) => Monoidal (PolySExp op) where
    unit = PolySExp hunit (\(Const ()) -> ()) (Const ())
    PolySExp op recon children ≪*≫ PolySExp op' recon' children'
        = PolySExp (hprod op op') 
                   (\(Product x y) -> (recon x, recon' y)) 
                   (Product children children')

instance (HMonoidal op) => Applicative (PolySExp op) where
    pure x = (\() -> x) <$> unit
    f <*> x = uncurry ($) <$> (f ≪*≫ x)

data SExp a = SExp a [SExp a]
    deriving (Show, Functor)

-- This is interesting!  We flatten everything, but we don't
-- necessarily have to; Builder here could be essentially a
-- mapping between a proper a and an S-expression
-- representation thereof.
data Builder f a = Builder a [SExp (f a)]
    deriving (Functor)

instance (Functor f) => Applicative (Builder f) where
    pure x = (\() -> x) <$> unit
    f <*> x = uncurry ($) <$> (f ≪*≫ x)


addFocus :: (a -> f a) -> Builder f a -> Builder f a
addFocus f (Builder x xhs) = Builder x [SExp (f x) xhs]

instance (Functor f) => IsoFunctor (Builder f)

instance (Functor f) => Monoidal (Builder f) where
    unit = Builder () []
    Builder x xhs ≪*≫ Builder y yhs
        = Builder (x,y) ((fmap.fmap.fmap) (,y) xhs ++ (fmap.fmap.fmap) (x,) yhs)

newtype Editor f a = Editor { runEditor :: a -> Maybe (f a) }

$( L.makePrisms ''Editor )

instance (Functor f) => IsoFunctor (Editor f) where
    isomap i = _Editor . L.dimapping (L.from i) (L.mapping (L.mapping i)) . L.from _Editor

instance (Applicative f) => Monoidal (Editor f) where
    unit = Editor (\() -> pure (pure ()))
    Editor f ≪*≫ Editor g = Editor $ \(x,y) -> (liftA2.liftA2) (,) (f x) (g y)

instance (Applicative f) => Grammar (Editor f) where
    empty = Editor (\_ -> Nothing)
    p ≪?≫ ed = Editor $ (fmap.fmap) (L.review p) . runEditor ed <=< L.preview p
    ed ≪|≫ ed' = Editor $ \x -> runEditor ed x <|> runEditor ed' x

instance (Applicative f) => Syntax (Editor f) where
    type SyntaxF (Editor f) = f
    char = Editor (\c -> pure (pure c))
    focus p = Editor . (fmap.fmap) p . runEditor

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


showNode :: (Show a) => Builder (Const String) a -> Builder (Const String) a
showNode = addFocus (Const . show)

data Ex f where
    Ex :: f a -> Ex f

data Op h = Op { getString :: forall f. h f -> String
               , toList :: forall f. h f -> [Ex f]
               }

data HWriter w a f = HWriter w (f a)

instance HFunctor (HWriter w a) where
    hfmap f (HWriter w x) = HWriter w (f x)

instance HMonoidal Op where
    hunit = Op 
        { getString = \_ -> ""
        , toList = \_ -> mempty
        }
    hprod op op' = Op 
        { getString = \(Product a b) -> getString op a ++ getString op' b
        , toList = \(Product a b) -> toList op a <> toList op' b
        }

logNode :: (Show a) => PolySExp Op a -> PolySExp Op a
logNode sexp = PolySExp op (\(HWriter _ (Identity a)) -> a) (HWriter (show (extract sexp)) sexp)
    where
    op = Op 
        { getString = \(HWriter s _) -> s
        , toList = \(HWriter _ xs) -> [Ex xs]
        }



listg :: (Grammar g) => g a -> g [a]
listg g = _Nil ≪?≫ unit
      ≪|≫ _Cons ≪?≫ g ≪:≫ listg g

nameg :: (Syntax g) => g Name 
nameg = listg char

expg :: (Syntax g, SyntaxF g ~ PolySExp Op) => g Exp
expg = focus logNode $
       _Lambda ≪?≫ nameg ≪:≫ expg
   ≪|≫ _App ≪?≫ expg ≪:≫ expg
   ≪|≫ _Var ≪?≫ nameg
   ≪|≫ _Let ≪?≫ listg defng ≪:≫ expg

defng :: (Syntax g, SyntaxF g ~ PolySExp Op) => g Defn
defng = focus logNode $ _Defn ≪?≫ nameg ≪:≫ expg


example :: Exp
example = App (Var "foo") (Var "bar")

polySExpToSExp :: PolySExp Op a -> SExp String
polySExpToSExp (PolySExp op _ children) = 
    SExp (getString op children) (map (\(Ex c) -> polySExpToSExp c) (toList op children))

main :: IO ()
main = do
    print $ polySExpToSExp <$> runEditor expg example
