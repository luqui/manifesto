{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import           Data.Functor.Compose
import qualified Rank2

import           Grammar

-- Stuff that should belong in a library.

-- We would abstract this Const stuff but we would need to convert between
-- (:*:) and (,), not worth it.
_constant :: (Eq a) => a -> HPrism (Const ()) (Const a)
_constant x = Prism (\_ -> Const x)
                    (\(Const x') -> if x == x' then Just (Const ()) else Nothing)

_Nil :: HPrism (Const ()) (Const [a])
_Nil = Prism (\_ -> Const [])
             (\case Const [] -> Just (Const ())
                    _ -> Nothing)

_Cons :: HPrism (Const a :*: Const [a]) (Const [a])
_Cons = Prism (\(Pair (Const x) (Const xs)) -> Const (x:xs))
              (\case Const (x:xs) -> Just (Pair (Const x) (Const xs))
                     _ -> Nothing)

_Just :: HPrism a (Compose Maybe a)
_Just = Prism (\x -> Compose (Just x))
              (\case Compose (Just x) -> Just x
                     _ -> Nothing)

_Nothing :: HPrism (Const ()) (Compose Maybe a)
_Nothing = Prism (\_ -> Compose Nothing)
                 (\case Compose Nothing -> Just (Const ())
                        _ -> Nothing)

many :: (Grammar g) => g (Const a) -> g (Const [a])
many g = _Nil ≪?≫ unit ≪|≫ many1 g

many1 :: (Grammar g) => g (Const a) -> g (Const [a])
many1 g = _Cons ≪?≫ g ≪*≫ many g

-- XXX how to do this without duplicating g?
chainr1 :: (Grammar g, Locus h g) => HPrism (Only (L h) :*: Only (L h)) h -> g (Const ()) -> g (Only (L h)) -> g (Only (L h))
chainr1 p op g = g 
             ≪|≫ locus (p ≪?≫ g ≪*≫ op *≫ chainr1 p op g)

-- There's got to be a better way to do this.
digit :: (Syntax g) => g (Const Integer)
digit = choice [ _constant n ≪?≫ symbol (show n) | n <- [0..9] ]

_digits :: HPrism (Const [Integer]) (Const Integer)
_digits = Prism (\(Const ds) -> Const (foldl (\n d -> 10*n + d) 0 ds))
                (\(Const n) -> Just (Const (toDigits n)))
    where
    toDigits' 0 = []
    toDigits' n | (d,r) <- n `divMod` 10 = r : toDigits d
    
    toDigits n = case reverse (toDigits' n) of
                    [] -> [0]
                    xs -> xs

number :: (Syntax g) => g (Const Integer)
number = _digits ≪?≫ many1 digit


varname :: (Syntax g) => g (Const String)
varname = choice [ _constant n ≪?≫ symbol n | n <- ["x","y","z"] ]


-- The example begins.
data Expr f
    = Lit (f (Literal Integer))
    | Let (f (Literal String)) (f (L Expr)) (f (L Expr))
    | Add (f (L Expr)) (f (L Expr))

-- These should be automatically generated.
_Lit :: HPrism (Only (Literal Integer)) Expr
_Lit = Prism (\(Only l) -> Lit l)
             (\case Lit l -> Just (Only l)
                    _ -> Nothing)

_Let :: HPrism (Only (Literal String) :*: Only (L Expr) :*: Only (L Expr)) Expr
_Let = Prism (\(Pair (Only a) (Pair (Only b) (Only c))) -> Let a b c)
             (\case Let a b c -> Just (Pair (Only a) (Pair (Only b) (Only c)))
                    _ -> Nothing)

_Add :: HPrism (Only (L Expr) :*: Only (L Expr)) Expr
_Add = Prism (\(Pair (Only a) (Only b)) -> Add a b)
             (\case Add a b -> Just (Pair (Only a) (Only b))
                    _ -> Nothing)

-- The grammar.
-- We collect the types that need to be given semantics into the synonym 'Loci'.
type Loci g = (Syntax g, Locus Expr g, Locus (LiteralF Integer) g, Locus (LiteralF String) g)

-- Concrete syntax.
expr :: forall g. (Loci g) => g (Only (L Expr))
expr = choice
    [ chainr1 _Add (symbol " + ") atom
    , locus (symbol "let " *≫ (_Let ≪?≫ literal varname ≪*≫ symbol " = " *≫ expr ≪*≫ symbol " in " *≫ expr))
    ]
    where
    atom = choice
        [ locus (_Lit ≪?≫ literal number)
        , symbol "(" *≫ expr ≪* symbol ")"
        ] 
{-
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


-- Navigation semantics
data NavSem l where
    NavSem :: (NavAssumptions (NavSem (L h)) h)
           => StringPrinter h
           -> NavSem (L h)

instance Semantics NavSem (LiteralF Char) where
    sem :: LiteralF Char NavSem -> NavSem (L (LiteralF Char))
    sem (Literal c) = NavSem 

    locus :: StringPrinter h -> StringPrinter (Only (L h))



{-
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
-}
-}

main = return ()
