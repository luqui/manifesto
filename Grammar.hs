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
import qualified Data.Text.Prettyprint.Doc as PP
import Control.Applicative (liftA2, (<|>))
import Control.Comonad (Comonad(..))
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad ((<=<), join)
import Data.Monoid (Monoid(..), First(..))

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


----------------- S expression builder -----------------

data SExp a = SExp a [SExp a]
    deriving (Show, Functor)

-- This is interesting!  We flatten everything, but we don't
-- necessarily have to; Builder here could be essentially a
-- mapping between a proper a and an S-expression
-- representation thereof.
data Builder f a = Builder a [SExp (f a)]
    deriving (Functor, Show)

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


------------------- tangible values --------------------------

data View v a = View v a
    deriving (Functor)

vConsWith :: (TupleCons t a b) => (v -> v' -> v'') -> View v a -> View v' b -> View v'' t
vConsWith f (View v x) (View v' x') = View (f v v') (L.view consiso (x,x'))

(<+>) :: (TupleCons t a b) => View (PP.Doc s) a -> View (PP.Doc s) b -> View (PP.Doc s) t
(<+>) = vConsWith (PP.<+>)

------------------- interactive editor -----------------------


data Input = ILeft | IRight | IUp | IDown | IChar Char
    deriving (Show)

newtype InputF a = InputF { runInputF :: Input -> First a }
    deriving (Functor, Semigroup, Monoid)

newtype Nav a = Nav { runNav :: Cofree InputF (Focus a) }
    deriving (Functor)

cat :: (Semigroup m) => Nav m -> Nav m -> Nav m
cat m n = uncurry (<>) <$> adjacent m n

data Focused = Focused | Unfocused
    deriving (Eq,Ord,Show)

instance Semigroup Focused where
    Focused <> Focused = Focused
    _ <> _ = Unfocused

instance Monoid Focused where
    mempty = Focused  -- seems strange, but it's indeed the unit of <>

type Focus = (->) Focused

adjacent :: Nav a -> Nav b -> Nav (a, b)
adjacent = \(Nav n) (Nav n') -> Nav (leftCont n n')
    where
    leftCont (x :< xi) ys = (\foc -> (x (foc <> Focused), extract ys (foc <> Unfocused))) :< 
        ((\xs -> leftCont xs ys) <$> xi) <> InputF (\case
            IRight -> pure (rightCont (x :< xi) ys)
            _ -> mempty)
    rightCont xs (y :< yi) = (\foc -> (extract xs (foc <> Unfocused), y (foc <> Focused))) :< 
        ((\ys -> rightCont xs ys) <$> yi) <> InputF (\case
            ILeft -> pure (leftCont xs (y :< yi))
            _ -> mempty)

string :: String -> Nav String
string s = Nav $ render :< InputF (\case
    IChar c -> pure (runNav (string (s ++ [c])))
    _ -> mempty)
    where
    render Unfocused = s
    render Focused = "{" ++ s ++ "}"
       

simNav :: (Show a) => Nav a -> IO ()
simNav = go . runNav
    where
    go (x :< xs) = do
        print (x Focused)
        line <- getLine
        let inp = case line of
                    "left" -> Just ILeft
                    "right" -> Just IRight
                    "up" -> Just IUp
                    "down" -> Just IDown
                    [c] -> Just (IChar c)
                    _ -> Nothing
        maybe (putStrLn "no" >> go (x :< xs)) go $ join (getFirst . runInputF xs <$> inp) 


------------------- destructuring traversal -------------------


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

listg :: (Grammar g) => g a -> g [a]
listg g = _Nil ≪?≫ unit
      ≪|≫ _Cons ≪?≫ g ≪:≫ listg g

nameg :: (Syntax g) => g Name 
nameg = listg char

expg :: (Syntax g, SyntaxF g ~ Builder (Const String)) => g Exp
expg = focus showNode $
       _Lambda ≪?≫ nameg ≪:≫ expg
   ≪|≫ _App ≪?≫ expg ≪:≫ expg
   ≪|≫ _Var ≪?≫ nameg
   ≪|≫ _Let ≪?≫ listg defng ≪:≫ expg

defng :: (Syntax g, SyntaxF g ~ Builder (Const String)) => g Defn
defng = focus showNode $ _Defn ≪?≫ nameg ≪:≫ expg


example :: Exp
example = App (Var "foo") (Var "bar")

main :: IO ()
main = do
    print $ runEditor expg example
