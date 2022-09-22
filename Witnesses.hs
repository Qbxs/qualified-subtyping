{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
module Witnesses where

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
    Refl    :: t :< TyFlipPol t
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

data Witness (pol :: Polarity) (pred :: Predicate pol) (t :: Typ pol) where
    Instance :: () -> Witness pol a t -- get any instance
    CoV      :: Witness Pos pred (TyFlipPol t) -> s :< t -> Witness Pos pred s
    ContraV  :: Witness Neg pred (TyFlipPol t) -> t :< s -> Witness Neg pred s

showableNat :: Witness Pos Showable Nat
showableNat = CoV (Instance ()) Prim

defaultableInt :: Witness Neg Defaultable (Inter Int' Top)
defaultableInt = ContraV (Instance ()) (Proj1 Refl)