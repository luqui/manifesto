{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
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


newtype Editor i h = Editor { runEditor :: i -> Located h -> First (Located h, Editor i h) }
    deriving (Semigroup, Monoid)

type Open r = r -> r

basicMotion :: Open (Editor Char h)
basicMotion cont = mconcat  
    [ entry 'h' smallleft
    , entry 'H' (drill downFirst)
    , entry 'l' smallright
    , entry 'L' (drill downLast)
    , entry 'j' left
    , entry 'J' (drill left)
    , entry 'k' right
    , entry 'K' (drill right)
    , entry 'o' up  -- o for "out"
    , entry 'O' (drill up)
    ]
    where
    up (Located (f:fs) e) = return $ Located fs (fillFrame f e)
    up _ = mempty

    downFirst (Located fs (Sexp h (e:es))) = return $ Located (Frame h [] es : fs) e
    downFirst _ = mempty

    downLast (Located fs (Sexp h (reverse -> e:es))) = return $ Located (Frame h es [] : fs) e
    downLast _ = mempty

    left (Located (Frame h (l:ls) rs : fs) e) = return $ Located (Frame h ls (e:rs) : fs) l
    left _ = mempty

    right (Located (Frame h ls (r:rs) : fs) e) = return $ Located (Frame h (e:ls) rs : fs) r
    right _ = mempty

    smallright = downFirst <> right <> r
        where
        -- this will terminate because at some point up will fail
        r = up `andThen` (right <> r)

    smallleft = (left `andThen` drill downLast) <> up
    drill m = (m `andThen` drill m) <> return

    andThen f g l = f l >>= g

    entry c f = Editor $ \i l -> 
        if | i == c -> (, cont) <$> f l
           | otherwise -> mempty

textEditMode :: Open (Editor Char String)
textEditMode cont = Editor $ \i (Located cx (Sexp h es)) ->
    if | i == '\DEL' -> 
        return (Located cx (Sexp (init h) es), textEditMode cont)
       | i == '\ESC' ->
        return (Located cx (Sexp h es), cont)
       | otherwise -> 
        return (Located cx (Sexp (h ++ [i]) es), textEditMode cont)

editCommands :: Open (Editor Char String)
editCommands cont = Editor $ \i loc ->
    case i of
        'e' -> return (loc, textEditMode cont)
        'a' | Located fs (Sexp h es) <- loc
            -> return (Located (Frame h (reverse es) [] : fs) (Sexp "" []), textEditMode cont)
        'A' | Located (Frame h l r : fs) e <- loc
            -> return (Located (Frame h (e:l) r : fs) (Sexp "" []), textEditMode cont)
        'i' | Located fs (Sexp h es) <- loc
            -> return (Located (Frame h [] es : fs) (Sexp "" []), textEditMode cont)
        'I' | Located (Frame h l r : fs) e <- loc
            -> return (Located (Frame h l (e:r) : fs) (Sexp "" []), textEditMode cont)
        'd' | Located (Frame h ls (r:rs) : fs) _ <- loc
            -> return (Located (Frame h ls rs : fs) r, cont)
            | Located (Frame h (l:ls) [] : fs) _ <- loc
            -> return (Located (Frame h ls [] : fs) l, cont)
            | Located (Frame h [] [] : fs) _ <- loc
            -> return (Located fs (Sexp h []), cont)
        _ -> mempty

mainEditor :: Editor Char String
mainEditor = basicMotion c <> editCommands c
    where
    c = mainEditor


example :: Located String
example = Located [] $ Sexp "doc" [r, Sexp "subbby" [r], r]
    where
    r = Sexp "hello" [Sexp "good" [], Sexp "day" [Sexp "sir" [Sexp "or" [], Sexp "madam" []]], Sexp "how" [Sexp "art" [], Sexp "thou" []]]

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go example mainEditor
  where
    go s editor = do
        ANSI.clearScreen
        ANSI.setCursorPosition 0 0
        PP.putDoc . ansify $ viewLoc lispViewer s
        c <- getChar
        case runEditor editor c s of
            First Nothing -> go s editor
            First (Just (s', editor')) -> go s' editor'
    ansify = PP.alterAnnotations $ \case
        Focused -> [PP.bgColor PP.White, PP.color PP.Black]
