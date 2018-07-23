{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

class Frame a where
    data Dormant a :: *
    data Active a :: *

data SeqFrame a
instance (Frame a) => Frame (SeqFrame a) where
    data Dormant (SeqFrame a) = SeqDormant [Dormant a]
    data Active (SeqFrame a)
        = SeqWithin [Dormant a] (Active a) [Dormant a]
        | SeqBetween [Dormant a] [Dormant a]

class (Frame a) => Editor inp a where
    handle :: inp -> Active a -> Either (Dormant a) (Active a)

data Motion = MLeft | MRight

instance (Editor Motion a) => Editor Motion (SeqFrame a) where
    handle MLeft (SeqWithin ls x rs) =
        case handle MLeft x of
            Left dor  -> Right $ SeqBetween ls (dor:rs)
            Right act -> Right $ SeqWithin ls act rs
    handle MLeft (SeqBetween [] rs) = Left $ SeqDormant rs
    handle MLeft (SeqBetween (l:ls) rs) = Right $ SeqBetween ls (l:rs)

    handle MRight (SeqWithin ls x rs) =
        case handle MRight x of
            Left dor  -> Right $ SeqBetween (dor:ls) rs
            Right act -> Right $ SeqWithin ls act rs
    handle MRight (SeqBetween ls []) = Left $ SeqDormant ls
    handle MRight (SeqBetween ls (r:rs)) = Right $ SeqBetween (r:ls) rs
        
