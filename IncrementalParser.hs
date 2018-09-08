{-# LANGUAGE DeriveFunctor #-}

module IncrementalParser where

import Control.Monad (ap)
import Control.Applicative (Alternative(..))

data IP a
    = Definite a (Char -> IP a)
    | Indefinite (Char -> IP a)
    | Impossible
    deriving (Functor)

instance Monad IP where
    return x = Definite x (const Impossible)
    Definite x c >>= f =
        case f x of
            Definite y c' -> Definite y (\ch -> (c ch >>= f) <|> c' ch)
            Indefinite c' -> Indefinite (\ch -> (c ch >>= f) <|> c' ch)
            Impossible    -> Impossible

instance Applicative IP where
    pure = return
    (<*>) = ap

instance Alternative IP where
    empty = Impossible
    Impossible <|> p = p
    Indefinite c <|> p = Indefinite (\ch -> c ch <|> p)
    p <|> Impossible = p
    p <|> Indefinite c = Indefinite (\ch -> p <|> c ch)
    Definite _ c <|> Definite _ c' = Indefinite (\ch -> c ch <|> c' ch)

instance Semigroup (IP a) where
    (<>) = (<|>)

instance Monoid (IP a) where
    mempty = empty


char :: IP Char
char = Indefinite pure

symbol :: String -> IP ()
symbol [] = Definite () (const empty)
symbol (c:cs) = Definite () (\ch ->
    if c == ch
        then symbol cs
        else empty)

applyChar :: IP a -> Char -> IP a
applyChar Impossible _ = Impossible
applyChar (Indefinite c) ch = c ch
applyChar (Definite _ c) ch = c ch

applyPrefix :: IP a -> String -> IP a
applyPrefix = foldl applyChar
