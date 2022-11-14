module Predicates where

import Types
import Witnesses

import Data.Either (isLeft)

data Variance = Co | Contra
  deriving (Eq, Show)

data Predicate = Predicate Variance String Typ
  deriving Show

resolveInstance :: Predicate -> [Predicate] -> Maybe Predicate
resolveInstance _ [] = Nothing
resolveInstance pred@(Predicate var name ty) (inst@(Predicate var' name' ty'):preds)
  | name == name' && var == var' = case var of
    Co -> if isLeft (generateWitnesses [Subtype ty ty']) then pure inst else resolveInstance pred preds
    Contra -> if isLeft (generateWitnesses [Subtype ty' ty]) then pure inst else resolveInstance pred preds
  | otherwise = resolveInstance pred preds