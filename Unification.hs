{-# LANGUAGE GeneralizedNewtypeDeriving, MonadComprehensions, ScopedTypeVariables, TypeApplications #-}

module Unification where

import qualified Data.Map as Map
import Control.Applicative
import Control.Monad (MonadPlus)
import Control.Monad.Trans.State
import Data.Proxy
import Data.Typeable (TypeRep, Typeable, typeOf, typeRep)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

type KeyID = Integer
data HeteroMap = HeteroMap KeyID (Map.Map (KeyID, TypeRep) Any)
newtype Key a = Key KeyID
    deriving (Eq,Ord)

emptyHM :: HeteroMap
emptyHM = HeteroMap 0 Map.empty

newHM :: (Typeable a) => a -> HeteroMap -> (HeteroMap, Key a)
newHM v (HeteroMap maxkey mp) = (HeteroMap (succ maxkey) (Map.insert (maxkey, typeOf v) (unsafeCoerce v) mp), Key maxkey)

adjustHM :: forall a. (Typeable a) => (a -> a) -> Key a -> HeteroMap -> HeteroMap
adjustHM f (Key key) (HeteroMap maxkey mp) = HeteroMap maxkey (Map.adjust (unsafeCoerce . f . unsafeCoerce) (key, typeRep (Proxy @a)) mp)

setHM :: (Typeable a) => Key a -> a -> HeteroMap -> HeteroMap
setHM k v = adjustHM (const v) k

lookupHM :: forall a. (Typeable a) => Key a -> HeteroMap -> Maybe a
lookupHM (Key key) (HeteroMap _maxkey mp) = unsafeCoerce <$> Map.lookup (key, typeRep (Proxy @a)) mp



newtype UnifT m a = UnifT { unUnifT :: StateT HeteroMap m a }
    deriving (Functor, Applicative, Alternative, Monad)

data VarCell a
    = Free
    | Ref (Var a)
    | Exact a

newtype Var a = Var (Key (VarCell a))

newVar :: (Typeable a, Monad m) => UnifT m (Var a)
newVar = UnifT $ do
    hm <- get
    let (hm', k) = newHM Free hm
    put hm'
    pure (Var k)

chaseRefs :: (Typeable a, Monad m) => Var a -> StateT HeteroMap m (Var a)
chaseRefs (Var k) = do
    hm <- get
    case lookupHM k hm of
        Nothing   -> error "empty HM cell"
        Just (Ref v) -> chaseRefs v  -- TODO squash
        _ -> pure (Var k)

unifyVars :: (Typeable a, Eq a, Monad m, MonadPlus m) => Var a -> Var a -> UnifT m ()
unifyVars v v' = UnifT $ do
    hm <- get
    Var k <- chaseRefs v
    Var k' <- chaseRefs v'
    case (lookupHM k hm, lookupHM k' hm) of
        (Just (Exact x), _) -> unUnifT (unifyVal (Var k') x)
        (_, Just (Exact y)) -> unUnifT (unifyVal (Var k) y)
        (Just Free, Just Free) -> put (setHM k (Ref (Var k')) hm)

        (Nothing, _) -> error "empty HM cell"
        (_, Nothing) -> error "empty HM cell"
        (Just (Ref _), _) -> error "ref not squashed"
        (_, Just (Ref _)) -> error "ref not squashed"

unifyVal :: (Typeable a, Eq a, Monad m, MonadPlus m) => Var a -> a -> UnifT m ()
unifyVal v x = UnifT $ do
    hm <- get
    Var k <- chaseRefs v
    case lookupHM k hm of
        Nothing -> error "empty HM cell"
        Just (Ref _) -> error "ref not squashed"
        Just Free -> put (setHM k (Exact x) hm)
        Just (Exact y) 
            | x == y -> pure ()
            | otherwise -> empty

runUnifT :: (Monad m) => UnifT m a -> m a
runUnifT (UnifT m) = evalStateT m emptyHM


test :: UnifT Maybe ()
test = do
    x <- newVar @Int
    y <- newVar @Int
    unifyVal x 1
    unifyVal y 2
    --unifyVars x y


main :: IO ()
main = print $ runUnifT test
    



{-
data FList a f
    = Nil
    | Cons (f (Literal a)) (f (L (FList a)))

append :: FList a f -> FList a f -> FList a f -> Logic ()
append xs ys zs = asum 
    [ [ () | Nil <- xs,       () <- ys .==. zs ]
    , [ () | Cons x xs <- xs, () <- append xs ys (Cons z zs) ]
    ]
-}
