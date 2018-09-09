{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}

module IncrementalParser where

import Control.Applicative (Alternative(..), liftA2)
import Data.Foldable (traverse_)
import Data.Monoid (First(..))

data Ambiguous a
    = Empty
    | Definite a
    | Indefinite
    deriving (Functor)

instance Show a => Show (Ambiguous a) where
    show Empty = "<empty>"
    show Indefinite = "<indefinite>"
    show (Definite x) = show x

instance Semigroup (Ambiguous a) where
    Empty <> x = x
    Indefinite <> _ = Indefinite
    x <> Empty = x
    _ <> _ = Indefinite

instance Monoid (Ambiguous a) where
    mempty = Empty

instance Applicative Ambiguous where
    pure = Definite

    Empty <*> _ = Empty
    Definite f <*> x = f <$> x
    --Indefinite <*> Empty = Empty  -- Though technically correct, this is not lazy enough
                                    -- for our purposes.
    Indefinite <*> _ = Indefinite

instance Alternative Ambiguous where
    empty = mempty
    (<|>) = (<>)

instance Syntax Ambiguous where
    erase Empty = Empty
    erase _ = Definite ()
    matchingChar _ = Indefinite

class (Alternative p) => Syntax p where
    erase :: p a -> p ()
    matchingChar :: (Char -> Bool) -> p Char

data Parser a = Parser (Ambiguous a) (First a) (Maybe (Char -> Parser a))
    deriving (Functor)

instance Applicative Parser where
    pure x = Parser (pure x) (pure x) mempty
    Parser fr fv fc <*> ~x@(Parser xr xv xc) = 
        Parser (fr <*> xr)
               (fv <*> xv)
               ((fmap.fmap) (<*> x) fc
                <|> liftA2 (fmap . fmap) (getFirst fv) xc)

instance Semigroup (Parser a) where
    Parser xr xv xc <> ~(Parser yr yv yc) = 
        Parser (xr <> yr)
               (xv <> yv)
               (xc <> yc)

instance Monoid (Parser a) where
    mempty = Parser mempty mempty mempty

instance Alternative Parser where
    empty = mempty
    (<|>) = (<>)

instance Syntax Parser where
    erase (Parser xr xv xc) = Parser (erase xr) (() <$ xv) ((fmap.fmap) erase xc)
    matchingChar p = Parser Indefinite mempty . pure $ \ch ->
        if p ch then pure ch else mempty
    
char :: (Syntax p) => p Char
char = matchingChar (const True)

exactChar :: (Syntax p) => Char -> p ()
exactChar ch = erase (matchingChar (== ch))

matching :: (Char -> Bool) -> Parser String
matching p = pure "" <|> ((:) <$> matchingChar p <*> matching p)

symbol :: String -> Parser ()
symbol = traverse_ exactChar

approximate :: Parser a -> Ambiguous a
approximate (Parser pr _ _) = pr

runParser :: Parser a -> (Maybe a, Maybe (Char -> Parser a))
runParser (Parser _ pv pc) = (getFirst pv, pc)

applyChar :: Parser a -> Char -> Parser a
applyChar p ch = maybe empty ($ ch) (snd (runParser p))

applyPrefix :: Parser a -> String -> Parser a
applyPrefix = foldl applyChar

get :: Parser a -> Maybe a
get = fst . runParser
