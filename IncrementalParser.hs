{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}

module IncrementalParser where

import Control.Applicative (Alternative(..))

data Ambiguous a
    = Empty
    | Indefinite
    | Definite a
    deriving (Functor)

instance Show a => Show (Ambiguous a) where
    show Empty = "<error>"
    show Indefinite = "<indefinite>"
    show (Definite x) = show x

eraseAmbig :: Ambiguous a -> Ambiguous ()
eraseAmbig Empty = Empty
eraseAmbig _ = Definite ()

instance Semigroup (Ambiguous a) where
    Empty <> x = x
    x <> Empty = x
    Indefinite <> _ = Indefinite
    _ <> Indefinite = Indefinite
    Definite _ <> Definite _ = Indefinite

instance Monoid (Ambiguous a) where
    mempty = Empty

instance Applicative Ambiguous where
    pure = Definite
    Empty <*> _ = Empty
    _ <*> Empty = Empty
    Indefinite <*> _ = Indefinite
    _ <*> Indefinite = Indefinite
    Definite f <*> Definite x = Definite (f x)

data Parser a = Ambiguous a :> Maybe (Char -> Parser a)
    deriving (Functor)

instance (Show a) => Show (Parser a) where
    show (x :> xs) = show x ++ maybe "" (const "...") xs

instance Semigroup (Parser a) where
    ~(x :> xc) <> ~(y :> yc) = (x <> y) :> (xc <> yc)

instance Monoid (Parser a) where
    mempty = mempty :> mempty

instance Applicative Parser where
    pure x = Definite x :> Nothing

    (f :> fc) <*> (x :> xc) = 
        (f <*> x) :> ((fmap.fmap) (<*> (x :> xc)) fc
                  <|> (fmap.fmap) ((f :> fc) <*>) xc)
                                                

instance Alternative Parser where
    empty = mempty
    (<|>) = (<>)

char :: Parser Char
char = Empty :> Just pure

matchingChar :: (Char -> Bool) -> Parser Char
matchingChar p = Empty :> Just (\ch -> if p ch then pure ch else empty)

matching :: (Char -> Bool) -> Parser String
matching p = pure "" <|> ((:) <$> matchingChar p <*> matching p)

symbol :: String -> Parser ()
symbol [] = Definite () :> Nothing
symbol (c:cs) = Empty :> Just (\ch ->
    if c == ch
        then symbol cs
        else empty)

-- This is key!  Semantically almost the same as fmap (const ()), but
-- since the result is now completely predictable, Indefinite results
-- become Definite ().
erase :: Parser a -> Parser ()
erase (x :> c) = eraseAmbig x :> (fmap.fmap) erase c

applyChar :: Parser a -> Char -> Parser a
applyChar (_ :> Nothing) _ = empty
applyChar (_ :> Just c) ch = c ch

applyPrefix :: Parser a -> String -> Parser a
applyPrefix = foldl applyChar

get :: Parser a -> Ambiguous a
get (x :> _) = x
