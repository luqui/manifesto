{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Grammar2 where

import Control.Applicative (liftA2)
import Control.Lens (Prism', prism', Iso', iso, preview, review)
import Control.Monad ((<=<))
import Data.Type.Coercion (Coercion(..), coerceWith)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Data.Roles (Representational(..))
import Rank2 (Product(..), Only(..))

type (:*:) = Product

-- A shape prism.  No funny business on the f, we use enough structural
-- isomorphisms that you could mess everything up that way.
type HPrism h' h = forall f. Representational f => Prism' (h' f) (h f)

-- Orphan!
instance Representational Identity where
    rep Coercion = Coercion

infixr 4 ≪?≫
infixr 5 ≪*≫, ≪*, *≫
infixr 3 ≪|≫
-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    (≪?≫) :: HPrism h' h -> g h -> g h'
    unit  :: g (Const ())
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    empty :: g h
    (≪|≫) :: g h -> g h -> g h

(*≫) :: (Grammar g) => g (Const ()) -> g h -> g h
s *≫ g = leftUnit ≪?≫ (s ≪*≫ g)
    where
    leftUnit :: Iso' (h f) ((Const () :*: h) f)
    leftUnit = iso (\x -> Pair (Const ()) x) (\(Pair (Const ()) x) -> x) 

(≪*) :: (Grammar g) => g h -> g (Const ()) -> g h
g ≪* s = rightUnit ≪?≫ (g ≪*≫ s)
    where
    rightUnit :: Iso' (h f) ((h :*: Const ()) f)
    rightUnit = iso (\x -> Pair x (Const ())) (\(Pair x (Const ())) -> x) 

choice :: (Grammar g) => [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Const Char)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h Identity))

promoteConst :: (Grammar g, Locus (Const a) g) => g (Const a) -> g (Only a)
promoteConst = (shuf ≪?≫) . locus
    where
    shuf :: (Representational f) => Iso' (Only a f) (Only (Const a Identity) f)
    shuf = iso (\(Only a) -> Only (coerceWith (rep Coercion) a)) 
               (\(Only a) -> Only (coerceWith (rep Coercion) a))

{-
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }
newtype GParser h = GParser { runGParser :: Parser (h Parser) }

instance Grammar Parser where
instance Locus h Parser
-}

newtype StringPrinter h = StringPrinter { runStringPrinter :: h Identity -> First String }

instance Grammar StringPrinter where
    p ≪?≫ pp = StringPrinter (runStringPrinter pp <=< First . preview p)
    unit = StringPrinter (\(Const ()) -> pure "")
    pp ≪*≫ pp' = StringPrinter (\(Pair h h') -> liftA2 (<>) (runStringPrinter pp h) (runStringPrinter pp' h'))
    empty = StringPrinter (\_ -> mempty)
    pp ≪|≫ pp' = StringPrinter (\h -> runStringPrinter pp h <> runStringPrinter pp' h)

instance Syntax StringPrinter where
    symbol s = StringPrinter (\(Const ()) -> pure s)
    char = StringPrinter (\(Const c) -> pure [c])

instance Locus h StringPrinter where
    locus pp = StringPrinter (\(Only (Identity h)) -> runStringPrinter pp h)


class Semantics f h where
    sem :: h f -> Only (h Identity) f

newtype Annotate f h = Annotate { runAnnotate :: h Identity -> First (h f) }

instance (Representational f) => Grammar (Annotate f) where
    p ≪?≫ ann = Annotate (fmap (review p) . runAnnotate ann <=< First . preview p)
    unit = Annotate (\(Const ()) -> pure (Const ()))
    ann ≪*≫ ann' = Annotate (\(Pair h h') -> liftA2 Pair (runAnnotate ann h) (runAnnotate ann' h'))
    empty = Annotate (\_ -> mempty)
    ann ≪|≫ ann' = Annotate (\h -> runAnnotate ann h <> runAnnotate ann' h)
    -- This is almost exactly the same as StringPrinter above.  How can we automate this?
    -- Only Identity `Rank2.Arrow` Compose First (Only f)

instance (Representational f) => Syntax (Annotate f) where
    symbol = const unit
    char = Annotate (\(Const c) -> pure (Const c))

-- When we are annotating with f, we can only have loci on shapes that have
-- a defined semantics for f.
instance (Representational f, Semantics f h) => Locus h (Annotate f) where
    locus (Annotate ann) = Annotate (\(Only (Identity h)) -> sem <$> ann h)


type Expr = ExprF Identity
data ExprF f
    = Cat (f Expr) (f Expr)
    | Lit (f Char)

_Cat :: Prism' (ExprF f) ((Only Expr :*: Only Expr) f)
_Cat = prism' (\(Pair (Only a) (Only b)) -> Cat a b)
              (\case Cat a b -> Just (Pair (Only a) (Only b))
                     _ -> Nothing)

_Lit :: Prism' (ExprF f) (Only Char f)
_Lit = prism' (\(Only c) -> Lit c)
              (\case Lit c -> Just (Only c)
                     _ -> Nothing)

type Loci g = (Syntax g, Locus ExprF g, Locus (Const Char) g)

expr :: (Loci g) => g (Only Expr)
expr = locus $ choice
    [ symbol "(" *≫ (_Cat ≪?≫ expr ≪*≫ symbol " ++ " *≫ expr) ≪* symbol ")"
    , _Lit ≪?≫ promoteConst char
    ]

pattern I :: a -> Identity a
pattern I x = Identity x

exampleExpr :: Only Expr Identity
exampleExpr = Only (Identity (Cat (I (Cat (I (Lit (I 'a'))) (I (Lit (I 'b'))))) (I (Lit (I 'c')))))


newtype EvalSem a = EvalSem { getEvalSem :: String }

instance Representational EvalSem where rep Coercion = Coercion

instance Semantics EvalSem (Const Char) where
    sem (Const c) = Only (EvalSem [c])

instance Semantics EvalSem ExprF where
    sem (Cat x y) = Only . EvalSem $ getEvalSem x ++ getEvalSem y
    sem (Lit x) = Only . EvalSem $ getEvalSem x
    

main :: IO ()
main = do
    print $ runStringPrinter expr exampleExpr
    print . fmap (getEvalSem . fromOnly) $ runAnnotate expr exampleExpr
