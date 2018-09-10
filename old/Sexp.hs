{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SExp where

import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as PP
import qualified System.Console.ANSI as ANSI
import Data.Function (fix)
import Data.Monoid (Monoid(..), First(..), (<>), mconcat)
import System.IO (hSetBuffering, stdin, stdout, BufferMode(..))

data SExp h = SExp h [SExp h]
    deriving (Show, Functor)

data Frame h = Frame h [SExp h] [SExp h]
    deriving (Show, Functor)

fillFrame :: Frame h -> SExp h -> SExp h
fillFrame (Frame h l r) e = SExp h (reverse l ++ [e] ++ r)

type Context h = [Frame h]   -- inside-out

data Located h = Located (Context h) (SExp h)
    deriving (Show, Functor)


data Viewer h v = Viewer {
    viewExp   :: h -> [v] -> v,
    viewFocus :: v -> v
  }

view :: Viewer h v -> SExp h -> v
view viewer (SExp h subs) = viewExp viewer h (map (view viewer) subs)

viewFrame :: Viewer h v -> Frame h -> v -> v
viewFrame viewer (Frame h l r) fill =
    viewExp viewer h (map (view viewer) (reverse l) ++ [fill] ++ map (view viewer) r)

viewCx :: Viewer h v -> Context h -> v -> v
viewCx viewer cx v = foldl (flip (viewFrame viewer)) (viewFocus viewer v) cx

viewLoc :: Viewer h v -> Located h -> v
viewLoc viewer (Located cx e) = viewCx viewer cx (view viewer e)


data Style = Focused

lispViewer :: Viewer String (PP.Doc Style)
lispViewer = Viewer {
    viewExp = \h -> \case
        [] -> PP.parens (PP.pretty h)
        vs -> PP.parens (PP.pretty h PP.<+> PP.align (PP.sep vs)),
    viewFocus = PP.annotate Focused
  }


type Var = String

data ExpTag
    = TLambda
    | TApp
    | TVar String
    deriving Show

expViewer :: Viewer ExpTag (Bool -> Bool -> PP.Doc Style)
expViewer = Viewer {
    viewExp = \h args lp ap -> case h of
        TLambda | [var, body] <- args -> 
            mparens lp $ "\\" <> var False False <> "." PP.<+> body False False
        TApp | [f, x] <- args ->
            mparens ap $ f True False PP.<+> x True True
        TVar v -> PP.pretty v
        _ -> PP.parens $ PP.sep (PP.pretty (show h) : map (\f -> f True True) args),
    viewFocus = \v lp ap -> PP.annotate Focused (v lp ap)
    } 
    where
    mparens True = PP.parens
    mparens False = id

newtype Editor i h = Editor { runEditor :: i -> Located h -> First (Located h, Editor i h) }
    deriving (Semigroup, Monoid)

type Open r = r -> r

basicMotionHelp :: [String]
basicMotionHelp = [
    "Motions:",
    "  h,j : small/big step left",
    "  l,k : small/big step right",
    "  o : step out",
    "  <Shift>+<Motion>: \"drill\" (repeat as much as possible)"
    ]

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

    downFirst (Located fs (SExp h (e:es))) = return $ Located (Frame h [] es : fs) e
    downFirst _ = mempty

    downLast (Located fs (SExp h (reverse -> e:es))) = return $ Located (Frame h es [] : fs) e
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
textEditMode cont = Editor $ \i (Located cx (SExp h es)) ->
    if | i == '\DEL' -> 
        return (Located cx (SExp (init h) es), textEditMode cont)
       | i == '\ESC' ->
        return (Located cx (SExp h es), cont)
       | otherwise -> 
        return (Located cx (SExp (h ++ [i]) es), textEditMode cont)

editHelp :: [String]
editHelp = [
    "Edits:",
    "  e : edit head",
    "  a,A : new child/sibling after",
    "  i,I : new child/sibling before",
    "  d : delete",
    "  <Esc>: exit edit mode" ]
    

editCommands :: Open (Editor Char String)
editCommands cont = Editor $ \i loc ->
    case i of
        'e' -> return (loc, textEditMode cont)
        'a' | Located fs (SExp h es) <- loc
            -> return (Located (Frame h (reverse es) [] : fs) (SExp "" []), textEditMode cont)
        'A' | Located (Frame h l r : fs) e <- loc
            -> return (Located (Frame h (e:l) r : fs) (SExp "" []), textEditMode cont)
        'i' | Located fs (SExp h es) <- loc
            -> return (Located (Frame h [] es : fs) (SExp "" []), textEditMode cont)
        'I' | Located (Frame h l r : fs) e <- loc
            -> return (Located (Frame h l (e:r) : fs) (SExp "" []), textEditMode cont)
        'd' | Located (Frame h ls (r:rs) : fs) _ <- loc
            -> return (Located (Frame h ls rs : fs) r, cont)
            | Located (Frame h (l:ls) [] : fs) _ <- loc
            -> return (Located (Frame h ls [] : fs) l, cont)
            | Located (Frame h [] [] : fs) _ <- loc
            -> return (Located fs (SExp h []), cont)
        _ -> mempty

mainEditor :: Editor Char String
mainEditor = basicMotion c <> editCommands c
    where
    c = mainEditor


example :: Located String
example = Located [] $ SExp "doc" [r, SExp "subbby" [r], r]
    where
    r = SExp "hello" [SExp "good" [], SExp "day" [SExp "sir" [SExp "or" [], SExp "madam" []]], SExp "how" [SExp "art" [], SExp "thou" []]]

exampleExp :: Located ExpTag
exampleExp = Located [] $ SExp TLambda [SExp (TVar "f") [], 
    SExp TApp [
        SExp TLambda [SExp (TVar "x") [], SExp TApp [SExp (TVar "f") [], SExp TApp [SExp (TVar "x") [], SExp (TVar "x") []]]],
        SExp TLambda [SExp (TVar "x") [], SExp TApp [SExp (TVar "f") [], SExp TApp [SExp (TVar "x") [], SExp (TVar "x") []]]]
    ]]


main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go lispViewer example mainEditor
  where
    go viewer s editor = do
        ANSI.clearScreen
        ANSI.setCursorPosition 0 0
        PP.renderIO stdout . PP.layoutPretty options . ansify $ viewLoc viewer s
        putStrLn . unlines $ ["",""] ++ basicMotionHelp ++ [""] ++ editHelp
        c <- getChar
        case runEditor editor c s of
            First Nothing -> go viewer s editor
            First (Just (s', editor')) -> go viewer s' editor'
    ansify = PP.alterAnnotations $ \case
        Focused -> [PP.bgColor PP.White, PP.color PP.Black]
    options = PP.LayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine 50 1.0 }
