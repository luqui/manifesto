{-# OPTIONS -fdefer-type-errors -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module Sexp where

import qualified Data.Text.Prettyprint.Doc as PP
import qualified System.Console.ANSI as ANSI
import Data.Monoid (Monoid(..), First(..), (<>), mconcat)
import System.IO (hSetBuffering, stdin, BufferMode(..))

data Sexp h = Sexp h [Sexp h]
    deriving (Show)

data Frame h = Frame h [Sexp h] [Sexp h]
    deriving (Show)

fillFrame :: Frame h -> Sexp h -> Sexp h
fillFrame (Frame h l r) e = Sexp h (l ++ [e] ++ r)

type Context h = [Frame h]   -- inside-out

data Located h = Located (Context h) (Sexp h)
    deriving (Show)


data Viewer h v = Viewer {
    viewExp   :: h -> [v] -> v,
    viewFocus :: v -> v
  }

view :: Viewer h v -> Sexp h -> v
view viewer (Sexp h subs) = viewExp viewer h (map (view viewer) subs)

viewFrame :: Viewer h v -> Frame h -> v -> v
viewFrame viewer (Frame h l r) fill =
    viewExp viewer h (map (view viewer) (reverse l) ++ [fill] ++ map (view viewer) r)

viewCx :: Viewer h v -> Context h -> v -> v
viewCx viewer cx v = foldl (flip (viewFrame viewer)) (viewFocus viewer v) cx

viewLoc :: Viewer h v -> Located h -> v
viewLoc viewer (Located cx e) = viewCx viewer cx (view viewer e)

lispViewer :: (Show h) => Viewer h (PP.Doc ann)
lispViewer = Viewer {
    viewExp = \h vs -> "(" <> PP.sep (PP.pretty (show h) : vs) <> ")",
    viewFocus = \v -> "{" <> v <> "}"
  }


newtype Editor i h = Editor { runEditor :: i -> Located h -> First (Located h) }
    deriving (Semigroup, Monoid)

basicMotion :: Editor Char h
basicMotion = mconcat  
    [ entry 'j' down
    , entry 'k' up
    , entry 'h' left
    , entry 'l' right
    ]
    where
    up (Located (f:fs) e) = Just $ Located fs (fillFrame f e)
    up _ = Nothing

    down (Located fs (Sexp h (e:es))) = Just $ Located (Frame h [] es : fs) e
    down _ = Nothing

    left (Located (Frame h (l:ls) rs : fs) e) = Just $ Located (Frame h ls (e:rs) : fs) l
    left _ = Nothing

    right (Located (Frame h ls (r:rs) : fs) e) = Just $ Located (Frame h (e:ls) rs : fs) r
    right _ = Nothing

    entry c f = Editor $ \i l -> 
        if | i == c -> First (f l)
           | otherwise -> First Nothing

example :: Located String
example = Located [] (Sexp "hello" [Sexp "good" [], Sexp "day" [Sexp "sir" [Sexp "or" [], Sexp "madam" []]], Sexp "how" [Sexp "art" [], Sexp "thou" []]])

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go example
  where
    go s = do
        ANSI.clearScreen
        ANSI.setCursorPosition 0 0
        print $ viewLoc lispViewer s
        c <- getChar
        case runEditor basicMotion c s of
            First Nothing -> go s
            First (Just s') -> go s'
