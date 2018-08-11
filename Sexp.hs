{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Sexp where

import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as PP
import qualified System.Console.ANSI as ANSI
import Data.Monoid (Monoid(..), First(..), (<>), mconcat)
import System.IO (hSetBuffering, stdin, BufferMode(..))

data Sexp h = Sexp h [Sexp h]
    deriving (Show)

data Frame h = Frame h [Sexp h] [Sexp h]
    deriving (Show)

fillFrame :: Frame h -> Sexp h -> Sexp h
fillFrame (Frame h l r) e = Sexp h (reverse l ++ [e] ++ r)

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


data Style = Focused

lispViewer :: (Show h) => Viewer h (PP.Doc Style)
lispViewer = Viewer {
    viewExp = \h -> \case
        [] -> PP.parens (PP.pretty (show h))
        vs -> PP.parens (PP.pretty (show h) PP.<+> PP.align (PP.sep vs)),
    viewFocus = \v -> PP.annotate Focused v
  }


newtype Editor i h = Editor { runEditor :: i -> Located h -> First (Located h) }
    deriving (Semigroup, Monoid)

basicMotion :: Editor Char h
basicMotion = mconcat  
    [ entry 'k' up
    , entry 'h' synleft
    , entry 'l' synright
    ]
    where
    up (Located (f:fs) e) = First . Just $ Located fs (fillFrame f e)
    up _ = mempty

    downFirst (Located fs (Sexp h (e:es))) = First . Just $ Located (Frame h [] es : fs) e
    downFirst _ = mempty

    downLast (Located fs (Sexp h (reverse -> e:es))) = First . Just $ Located (Frame h es [] : fs) e
    downLast _ = mempty

    left (Located (Frame h (l:ls) rs : fs) e) = First . Just $ Located (Frame h ls (e:rs) : fs) l
    left _ = mempty

    right (Located (Frame h ls (r:rs) : fs) e) = First . Just $ Located (Frame h (e:ls) rs : fs) r
    right _ = mempty

    synright = downFirst <> right <> r
        where
        -- this will terminate because at some point up will fail
        r = up `andThen` (right <> r)

    synleft = (left `andThen` drillDown) <> up
        where
        drillDown = (downLast `andThen` drillDown) <> nomotion

    andThen f g l = First $ getFirst (f l) >>= getFirst . g

    nomotion = First . Just

    entry c f = Editor $ \i l -> 
        if | i == c -> f l
           | otherwise -> mempty

example :: Located String
example = Located [] $ Sexp "doc" [r, Sexp "subbby" [r], r]
    where
    r = Sexp "hello" [Sexp "good" [], Sexp "day" [Sexp "sir" [Sexp "or" [], Sexp "madam" []]], Sexp "how" [Sexp "art" [], Sexp "thou" []]]

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go example
  where
    go s = do
        ANSI.clearScreen
        ANSI.setCursorPosition 0 0
        PP.putDoc . ansify $ viewLoc lispViewer s
        c <- getChar
        case runEditor basicMotion c s of
            First Nothing -> go s
            First (Just s') -> go s'
    ansify = PP.alterAnnotations $ \case
        Focused -> [PP.bgColor PP.White, PP.color PP.Black]
