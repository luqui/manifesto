{-# OPTIONS -Wall #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import qualified Control.Lens as L

import Monoidal
import Grammar
import qualified Nav

type Name = String

data Exp
    = Lambda Name Exp
    | App Exp Exp
    | Var Name
    | Let [Defn] Exp
    deriving (Read, Show)

data Defn
    = Defn Name Exp
    deriving (Read, Show)

$( L.makePrisms ''Exp )
$( L.makePrisms ''Defn )

expg :: (Syntax g) => g Exp
expg = focus $
       _Lambda ≪?≫ (symbol "\\" *≫ nameg ≪* symbol ". ")  ≪:≫ expg
   ≪|≫ _Let ≪?≫ (symbol "let " *≫ manyDelim (symbol "; ") defng ≪* symbol " in ") ≪:≫ expg
   ≪|≫ chainl1 (symbol " ") _App termg

termg :: (Syntax g) => g Exp
termg = focus (_Var ≪?≫ nameg)
    ≪|≫ parens expg

defng :: (Syntax g) => g Defn
defng = focus $ _Defn ≪?≫ (nameg ≪* symbol " = ") ≪:≫ expg

nameg :: (Syntax g) => g Name 
nameg = many char


example :: Exp
example = App (Var "foo") (Var "bar")

example2 :: Exp
example2 = Lambda "f" (Let [Defn "r" (App (Var "f") (Var "r")), Defn "r'" (App (Var "f") (Var "r'"))] (Var "r'"))

example3 :: Exp
example3 = Lambda "f" (App (Lambda "x" (App (Var "f") (App (Var "x") (Var "x"))))
                           (Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))))

data Input = ILeft | IRight | IUp | IDown | IChar Char

$( L.makePrisms ''Input )

instance Nav.NavInput Input where
    _ILeft = _ILeft
    _IRight = _IRight
    _IUp = _IUp
    _IDown = _IDown
    _IChar = _IChar

main :: IO ()
main = do
    let Just (Nav.FocNav nav) = runEditor (expg :: Editor Input () Exp) example3
    Nav.simNav nav
