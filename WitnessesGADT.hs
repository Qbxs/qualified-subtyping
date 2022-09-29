{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Witnesses where

main :: IO ()
main = pure ()

data Polarity = Pos | Neg

type family FlipPol (pol :: Polarity) where
    FlipPol Pos = Neg
    FlipPol Neg = Pos

data Typ (pol :: Polarity) where
    Top       :: Typ Neg
    Bot       :: Typ Pos
    Inter     :: Typ Neg -> Typ Neg -> Typ Neg
    Union     :: Typ Pos -> Typ Pos -> Typ Pos
    Int'      :: Typ pol
    Nat       :: Typ pol
    TyFlipPol :: Typ pol -> Typ (FlipPol pol)

data (:<) (t :: Typ Pos) (s :: Typ Neg) where
    Refl    :: TyFlipPol t :< t
    Trans   :: t :< s -> TyFlipPol s :< r -> t :< r
    FromTop :: t :< Top
    ToBot   :: Bot :< t
    Proj1   :: TyFlipPol t :< r -> TyFlipPol (Inter t s) :< r
    Proj2   :: TyFlipPol t :< r -> TyFlipPol (Inter s t) :< r
    In1     :: t :< TyFlipPol r -> t :< TyFlipPol (Union s r)
    In2     :: t :< TyFlipPol r -> t :< TyFlipPol (Union r s)
    Meet    :: t :< s -> t :< r -> t :< Inter s r
    Join    :: t :< r -> s :< r -> Union t s :< r 
    Prim    :: Nat :< Int'


data Predicate (pol :: Polarity) where
     Showable    :: Predicate Pos
     Defaultable :: Predicate Neg

newtype ShowDictionary t =
    ShowDictionary {
        show :: t -> String
    }

newtype DefaultDictionary t =
    DefaultDictionary {
        defaultVal :: t
    }

-- type family ToDict (pol :: Polarity) (pred :: Predicate pol) t where
--     ToDict Pos Showable t = ShowDictionary t
--     ToDict Neg Defaultable t = DefaultDictionary t

data Witness (pol :: Polarity) (pred :: Predicate pol) (t :: Typ pol) where
    Instance :: Predicate pol -> Typ pol -> Witness pol pred t
    CoV      :: Witness Pos pred (TyFlipPol t) -> s :< t -> Witness Pos pred s
    ContraV  :: Witness Neg pred (TyFlipPol t) -> t :< s -> Witness Neg pred s

-- derived rules
bot :: Witness Pos pred (TyFlipPol t) -> Witness Pos pred Bot
bot w = CoV w ToBot
top :: Witness Neg pred (TyFlipPol t) -> Witness Neg pred Top
top w = ContraV w FromTop
nat :: Witness Pos pred (TyFlipPol Int') -> Witness Pos pred Nat
nat w = CoV w Prim
int :: Witness Neg pred (TyFlipPol Nat) -> Witness Neg pred Int'
int w = ContraV w Prim
-- not typeable as is:
-- proj1 :: Witness Neg pred t -> Witness Neg pred (Inter t s)
-- proj1 w = ContraV w (Proj1 Refl)
-- proj2 :: Witness Neg pred t -> Witness Neg pred (Inter s t)
-- proj2 w = ContraV w (Proj2 Refl)
-- in1 :: Witness Pos pred t -> Witness Pos pred (Union t s)
-- in1 w = CoV w (In1 Refl)
-- in2 :: Witness Pos pred t -> Witness Pos pred (Union s t)
-- in2 w = CoV w (In2 Refl)

showableNat :: Witness Pos Showable Nat
showableNat = CoV (Instance Showable Int') Prim

defaultableInt :: Witness Neg Defaultable (Inter Int' Top)
defaultableInt = ContraV (Instance Defaultable Nat) (Proj1 Refl)
