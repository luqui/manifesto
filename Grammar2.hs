-- The (dual) category of rank-2 prisms.
newtype Prism h h' = HPrism (forall x. Prism (h' f) (h f))

-- A Grammar is a monoidal functor from some prism category to Hask.
class Grammar g where
    (≪*≫) :: g h -> g h' -> g (h :*: h')
    unit  :: g (Const ())
    (≪|≫) :: g h -> g h -> g h
    empty :: g h

    (≪+≫) :: g h -> g h' -> g (h :+: h')
    zero  :: g (Const Void)

    (≪?≫) :: HPrism h h' -> g h -> g h'

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
instance Locus h Parser -- no constraints!

newtype PrettyPrinter h = PrettyPrinter (h Identity -> Maybe Doc)
instance Grammar PrettyPrinter
instance Locus h PrettyPrinter -- no constraints!

class Semantics f h where
    sem :: h f -> Only (h Identity) f

newtype Annotate f h = Annotate (h Identity -> Maybe (h f))
instance Grammar (Annotate f)

class (Grammar g) => Locus h g where
    locus :: g h -> g (Only (h Identity))

-- When we are annotating with f, we can only have loci on shapes that have
-- a defined semantics for f.
instance (Semantics f h) => Locus h (Annotate f) where
    locus (Annotate ann) = Annotate (\(Only (Identity h)) -> sem <$> ann h)


expr :: (Locus ExprF g) => g (Only Expr)
expr = locus $ choice [
    _Add ≪?≫ expr ≪*≫ expr,
    _Lit ≪?≫ integer
  ] 

integer :: (Grammar g) => g (Only Integer)
integer = ...


-- For a more complex grammar, we should collect the loci into transitive closures
-- of what we need, e.g.
-- 
-- type Loci g = (Locus ExprF g, Locus DefnF g, Locus TypeF g)
--
-- Then most of our grammars will have signatures like
--
-- foo :: (Loci g) => g (Only Foo)
--
-- Which is about as concise as one could hope for.
