{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Grammar
import qualified Rank2
import qualified ApproximationParser as AP
import Data.Monoid (First(..))

-- The abstract syntax.  Note the pattern of recusion: f on top, I the
-- rest of the way down.
data Expr f
    = Cat (f (L Expr)) (f (L Expr))
    | Lit (f (Literal Char))

instance Rank2.Functor Expr where
    f <$> Cat a b = Cat (f a) (f b)
    f <$> Lit c = Lit (f c)

deriving instance (Show a) => Show (Expr (Const a)) 


-- These should be automatically generated.
_Cat :: HPrism (Only (L Expr) :*: Only (L Expr)) Expr
_Cat = Prism (\(Pair (Only a) (Only b)) -> Cat a b)
             (\case Cat a b -> Just (Pair (Only a) (Only b))
                    _ -> Nothing)

_Lit :: HPrism (Only (Literal Char)) Expr 
_Lit = Prism (\(Only c) -> Lit c)
             (\case Lit c -> Just (Only c)
                    _ -> Nothing)

-- The grammar.
-- We collect the types that need to be given semantics into the synonym 'Loci'.
type Loci g = (Syntax g, Locus Expr g, Locus (LiteralF Char) g)

-- Concrete syntax.
expr1 :: (Loci g) => g Expr
expr1 = choice
    [ symbol "cat(" *≫ (_Cat ≪?≫ expr ≪*≫ symbol "," *≫ expr) ≪* symbol ")"
    , symbol "'" *≫ (_Lit ≪?≫ literal char) ≪* symbol "'"
    ]

expr :: (Loci g) => g (Only (L Expr))
expr = locus expr1

-- Evaluation semantics. (It's a shame that we need to coerce for promoteConst,
-- that's what's causing all this Representational junk.  If not, EvalSem could
-- even be a GADT showing how to evaluate each type of representable thing.
-- There must be a better way.)
--
-- We give a semantics to each type required by Loci.
data family EvalSem (a :: Label) :: *
data instance EvalSem (Literal Char) = EChar Char
    deriving Show
data instance EvalSem (L Expr) = EStr String
    deriving Show


instance Semantics EvalSem (LiteralF Char) where
    sem (Literal c) = EChar c

instance Semantics EvalSem Expr where
    sem (Cat (EStr x) (EStr y)) = EStr (x ++ y)
    sem (Lit (EChar x)) = EStr [x]

-- Example expression.

exampleExpr :: Tree (L Expr)
exampleExpr = t (Cat (t (Cat (t (Lit (t (Literal 'a')))) (t (Lit (t (Literal 'b')))))) (t (Lit (t (Literal 'c')))))
    where
    t = Tree


main :: IO ()
main = do
    -- Pretty print.
    print $ runStringPrinter expr (Only exampleExpr)
    -- Evaluate.
    print (fromOnly <$> runAnnotate expr (Only exampleExpr) :: First (EvalSem (L Expr)))

    -- Annotate
    let ann = fromOnly <$> runAnnotate expr (Only exampleExpr) :: First (Annotated EvalSem (L Expr))
    case ann of
        First (Just (Annotated _ (Cat (Annotated a _) _))) -> print a
        _ -> putStrLn "pattern error"

    -- Parser
    print . AP.approximate . AP.applyPrefix (runGParser expr1) $ "cat("
