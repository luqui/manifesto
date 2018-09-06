-- The (dual) category of rank-2 (dual) prisms.
newtype HPrism h h' = HPrism (forall x. Prism (h' f) (h f))

-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    type Cat g :: ((k -> *) -> *) -> ((k -> *) -> *) -> *
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    unit  :: g (Const ())
    (≪|≫) :: g h -> g h -> g h
    empty :: g h
    (≪$≫) :: HPrism h h' -> g h -> g h'

(≪?≫) :: HPrism h h' -> g h' -> g h'
p ≪?≫ g = embedPrism p ≪$≫ g

(*≫) :: g (Const ()) -> g h -> g h
s *≫ g = leftUnit ≪?≫ (s ≪*≫ g)
    where
    leftUnit :: HPrism (Const () :*: h) h

choice :: [g h] -> g h
choice = foldr (≪|≫) empty

class (Grammar g) => Syntax g where
    symbol :: String -> g (Const ())
    char :: g (Only Char)
    (|+|) :: g h -> g h' -> g (h :*: h')

newtype Parser h = Parser (Parsec.Parser (h Identity))
instance Grammar Parser 

newtype PrettyPrinter h = PrettyPrinter (h Identity -> Maybe Doc)

instance Grammar PrettyPrinter

class Semantics f h where
    sem :: h f -> Only (h Identity) f

newtype Annotate f h = Annotate (h Identity -> Maybe (h f))
instance Grammar (Annotate f)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h Identity))

instance (Semantics f h) => Locus h (Annotate f) where
    locus (Annotate ann) = Annotate (\(Only (Identity h)) -> sem <$> ann h)


expr :: (Locus ExprF g, Grammar g) => g (Only Expr)
expr = locus $ choice [
    _Add ≪?≫ expr ≪*≫ expr,
    _Lit ≪?≫ integer
  ] 

integer :: Grammar g => g (Only Integer)
integer = ...


