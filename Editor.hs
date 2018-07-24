{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}

import Prelude hiding (id, (.))
import Control.Category
import System.IO (hSetBuffering, stdin, BufferMode(..))
import Control.Applicative hiding (optional)

data Iso a b = Iso (a -> b) (b -> a)

instance Category Iso where
    id = Iso id id
    Iso g g' . Iso f f' = Iso (g . f) (f' . g')

apply :: Iso a b -> a -> b
apply (Iso f _) = f

inverse :: Iso a b -> Iso b a
inverse (Iso f f') = Iso f' f



data Input = ILeft | IRight | IUp | IDown | IInsert Char

-- A machine with a transition monad m, hidden state s,
-- and observable state a.
data Machine m s a = Machine {
    mCreate  :: a -> s,
    mObserve :: s -> a,
    mInput   :: Input -> s -> m s 
  }

mapMachine :: Iso a b -> Machine m s a -> Machine m s b
mapMachine (Iso f f') (Machine {..}) = Machine {
    mCreate = mCreate . f',
    mObserve = f . mObserve,
    mInput = mInput
  }

data Editor a = forall s. View s => Editor (Machine Maybe s a)

mapEditor :: Iso a b -> Editor a -> Editor b
mapEditor iso (Editor m) = Editor (mapMachine iso m)


data EditorState a = forall s. View s => EditorState (Machine Maybe s a) s

editorMachine :: Editor a -> Machine Maybe (EditorState a) a
editorMachine e = Machine {
    mCreate = \a -> case e of Editor m -> EditorState m (mCreate m a),
    mObserve = \(EditorState m s) -> mObserve m s,
    mInput = \i (EditorState m s) -> EditorState m <$> mInput m i s
  }

instance View (EditorState a) where
    view (EditorState _ s) = view s


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

charMachine :: (Alternative m) => Machine m (Maybe Char) (Maybe Char)
charMachine = Machine {
    mCreate = id,
    mObserve = id,
    mInput = \i s -> case i of
        IInsert c | Nothing <- s -> pure (Just c)
        _ -> empty
  }

char :: Editor (Maybe Char)
char = Editor charMachine

data PairState sa sb a b
    = PairFocus a b
    | LeftFocus sa b
    | RightFocus a sb

instance (View sa, View sb, View a, View b) => View (PairState sa sb a b) where
    view (PairFocus a b) = "[" ++ view a ++ view b ++ "]"
    view (LeftFocus sa b) = view sa ++ view b
    view (RightFocus a sb) = view a ++ view sb

pairMachine :: (Alternative m) 
            => Machine m sa a -> Machine m sb b -> Machine m (PairState sa sb a b) (a,b)
pairMachine ma mb = Machine {
    mCreate = \(a,b) -> PairFocus a b,
    mObserve = \case
        PairFocus a b -> (a, b)
        LeftFocus sa b -> (mObserve ma sa, b)
        RightFocus a sb -> (a, mObserve mb sb),
    mInput = input
  }
    where
    input i (PairFocus a b) = case i of
        IInsert{} -> input i (LeftFocus (mCreate ma a) b)
        IDown -> pure $ LeftFocus (mCreate ma a) b
        _ -> empty
    input i (LeftFocus sa b) = (LeftFocus <$> mInput ma i sa <*> pure b) <|> (
        let rightfocus = RightFocus (mObserve ma sa) (mCreate mb b) in
        case i of 
            IRight -> pure rightfocus
            IUp    -> pure $ PairFocus (mObserve ma sa) b
            IInsert ch -> input (IInsert ch) rightfocus
            _ -> empty)
    input i (RightFocus a sb) = (RightFocus <$> pure a <*> mInput mb i sb) <|> (
        case i of 
            ILeft -> pure $ LeftFocus (mCreate ma a) (mObserve mb sb)  
            IUp   -> pure $ PairFocus a (mObserve mb sb)
            _ -> empty)

pair :: (View a, View b) => Editor a -> Editor b -> Editor (a,b)
pair (Editor ma) (Editor mb) = Editor (pairMachine ma mb)


optionalMachine :: (Alternative m, Default a) => Machine m s a -> Machine m (Maybe s) (Maybe a)
optionalMachine m = Machine {
    mCreate = const Nothing,
    mObserve = fmap (mObserve m),
    mInput = input
  }
    where
    input i Nothing = case i of
        IInsert{} -> input i (Just (mCreate m def))
        _ -> empty
    input i (Just s) = Just <$> mInput m i s

optional :: (Default a) => Editor a -> Editor (Maybe a)
optional e = Editor (optionalMachine (editorMachine e))

instance Default [a] where
    def = []

instance (View a) => View [a] where
    view [] = ""
    view (x:xs) = view x ++ view xs
 
test :: Editor String
test = mapEditor siso $ pair char (mapEditor liso $ optional test)
    where
    siso = Iso (\(x,xs) -> maybe xs (:xs) x) 
               (\case [] -> (Nothing, []); (x:xs) -> (Just x,xs))

    liso = Iso (maybe [] id) Just

main :: IO ()
main = do
    hSetBuffering stdin NoBuffering
    go test
  where
    go (Editor m) = do
        let s = mCreate m def
        step s
      where
        step s = do
            putStrLn $ view s
            i <- getChar >>= return . \case
                        'H' -> ILeft
                        'J' -> IDown
                        'K' -> IUp
                        'L' -> IRight
                        c   -> IInsert c
            putStrLn ""
            case mInput m i s of
                Nothing -> step s
                Just s' -> step s'
