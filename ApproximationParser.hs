{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}

module ApproximationParser where

import Control.Applicative (Alternative(..), liftA2)
import Data.Foldable (traverse_)
import Data.Monoid (First(..))

data Approx a
    = Empty
    | Definite a
    | Indefinite
    deriving (Functor)

instance Show a => Show (Approx a) where
    show Empty = "<empty>"
    show Indefinite = "<indefinite>"
    show (Definite x) = show x

instance Semigroup (Approx a) where
    Empty <> a = a
    Indefinite <> _ = Indefinite
    a <> Empty = a
    _ <> _ = Indefinite

instance Monoid (Approx a) where
    mempty = Empty

instance Applicative Approx where
    pure = Definite

    Empty <*> _ = Empty
    Definite f <*> x = f <$> x
    --Indefinite <*> Empty = Empty  -- Though technically correct, this is not lazy enough
                                    -- for our purposes.
    Indefinite <*> _ = Indefinite

instance Alternative Approx where
    empty = mempty
    (<|>) = (<>)

instance Syntax Approx where
    erase _ = Definite ()

    erase' Empty = Empty
    erase' _ = Definite ()
    matchingChar _ = Indefinite

class (Alternative p) => Syntax p where
    -- erase: non-strict erasue -- approximation always succeeds
    --  (use to erase infinite grammars to make them finitely approximable)
    erase :: p a -> p ()
    -- erase': strict erasure -- approximations allowed to fail
    --   (use to erase finite terms for "timely" approximations)
    erase' :: p a -> p ()
    matchingChar :: (Char -> Bool) -> p Char

data Parser a = Parser (Approx a) (First a) (Maybe (Char -> Parser a))
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
    erase' (Parser xr xv xc) = Parser (erase' xr) (() <$ xv) ((fmap.fmap) erase' xc)
    matchingChar p = Parser Indefinite mempty . pure $ \ch ->
        if p ch then pure ch else mempty
    
char :: (Syntax p) => p Char
char = matchingChar (const True)

exactChar :: (Syntax p) => Char -> p ()
exactChar ch = erase' (matchingChar (== ch))

matching :: (Char -> Bool) -> Parser String
matching p = pure "" <|> ((:) <$> matchingChar p <*> matching p)

symbol :: String -> Parser ()
symbol = traverse_ exactChar

approximate :: Parser a -> Approx a
approximate (Parser pr _ _) = pr

runParser :: Parser a -> (Maybe a, Maybe (Char -> Parser a))
runParser (Parser _ pv pc) = (getFirst pv, pc)

applyChar :: Parser a -> Char -> Parser a
applyChar p ch = maybe empty ($ ch) (snd (runParser p))

applyPrefix :: Parser a -> String -> Parser a
applyPrefix = foldl applyChar

get :: Parser a -> Maybe a
get = fst . runParser
