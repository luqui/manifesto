{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}

import Prelude hiding (id, (.))
import Control.Category
import Control.Arrow (left)
import System.IO (hSetBuffering, stdin, BufferMode(..))

data Iso a b = Iso (a -> b) (b -> a)

instance Category Iso where
    id = Iso id id
    Iso g g' . Iso f f' = Iso (g . f) (f' . g')

apply :: Iso a b -> a -> b
apply (Iso f _) = f

inverse :: Iso a b -> Iso b a
inverse (Iso f f') = Iso f' f



data Input = ILeft | IRight | IUp | IDown | IInsert Char

data Editor a = forall s. Editor {
    eCreate  :: a -> s,
    eInput   :: Input -> s -> Either a s,
    eView    :: s -> String
  }

mapE :: Iso a b -> Editor a -> Editor b
mapE (Iso f f') (Editor {..}) = Editor {
    eCreate = eCreate . f',
    eInput  = \i s -> left f (eInput i s),
    eView   = eView
  }

class Default a where
    def :: a

instance Default (Maybe a) where
    def = Nothing

instance (Default a, Default b) => Default (a,b) where
    def = (def, def)

class View a where
    view :: a -> String

instance View Char where
    view c = [c]

instance (View a) => View (Maybe a) where
    view Nothing = "_"
    view (Just x) = view x

instance (View a, View b) => View (a,b) where
    view (a,b) = view a ++ view b

char :: Editor (Maybe Char)
char = Editor {
    eCreate = id,
    eInput  = \i s -> case i of
        IInsert c | Nothing <- s -> Right (Just c)
        _ -> Left s,
    eView   = view
  }

pair :: (View a, View b) => Editor a -> Editor b -> Editor (a,b)
pair (Editor { eCreate = createA, eInput = inputA, eView = viewA }) 
     (Editor { eCreate = createB, eInput = inputB, eView = viewB }) 
    = Editor {
        eCreate = \(a, b) -> Left (createA a, b),
        eInput  = input,
        eView = \case
            Left (as, b) -> viewA as ++ view b
            Right (a, bs) -> view a ++ viewB bs
      }
    where
    input i (Left (as, b)) = case inputA i as of
        Left a' -> 
            let s' = Right (a', createB b) in
            input i s'
        Right as' -> Right (Left (as', b))
    input i (Right (a, bs)) = case inputB i bs of
        Left b' -> Left (a, b')
        Right bs' -> Right (Right (a, bs'))

test = pair char char

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go test
  where
    go (Editor {..}) = do
        let s = eCreate def
        step s
      where
        step s = do
            putStrLn $ eView s
            i <- getChar >>= return . \case
                        'H' -> ILeft
                        'J' -> IDown
                        'K' -> IUp
                        'L' -> IRight
                        c   -> IInsert c
            putStrLn ""
            case eInput i s of
                Left r -> putStrLn $ view r
                Right s' -> step s'
