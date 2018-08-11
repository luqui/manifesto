{-# OPTIONS -fdefer-type-errors -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Sexp where

import qualified Data.Text.Prettyprint.Doc as PP
import Data.Semigroup ((<>))

data Sexp h = Sexp h [Sexp h]
    deriving (Show)

data Frame h = Frame h [Sexp h] [Sexp h]
    deriving (Show)

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
    viewExp viewer h (map (view viewer) l ++ [fill] ++ map (view viewer) r)

viewCx :: Viewer h v -> Context h -> v -> v
viewCx viewer = flip (foldr (viewFrame viewer))

viewLoc :: Viewer h v -> Located h -> v
viewLoc viewer (Located cx e) = viewCx viewer cx (view viewer e)


lispViewer :: (Show h) => Viewer h (PP.Doc ann)
lispViewer = Viewer {
    viewExp = \h vs -> "(" <> PP.sep (PP.pretty (show h) : vs) <> ")",
    viewFocus = \v -> "{" <> v <> "}"
  }


