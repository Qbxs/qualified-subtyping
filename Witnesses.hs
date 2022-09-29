{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Witnesses where
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

main :: IO ()
main = pure ()

data Polarity = Pos | Neg
data Typ where
    Top       :: Typ
    Bot       :: Typ
    Inter     :: Typ -> Typ -> Typ
    Union     :: Typ -> Typ -> Typ
    Int'      :: Typ
    Nat       :: Typ

data (:<) where
    Refl    :: (:<)
    FromTop :: (:<)
    ToBot   :: (:<)
    Meet    :: (:<) -> (:<) -> (:<)
    Join    :: (:<) -> (:<) -> (:<)
    Prim    :: (:<)
    SubVar  :: Char -> (:<)

data Constraint where
    Subtype :: Typ -> Typ -> Constraint
    InComplete :: Char -> Constraint -> Constraint

solve :: [Constraint] -> SolverM [(:<)]
solve [] = pure []
solve ((InComplete v cnstr):cs) = do
    solve (cnstr:cs)
solve (cnstr:cs) = do
    (foo,bar) <- solveSubWithWitness cnstr
    tell [bar]
    solve (foo++cs)

-- | Apply all substitutions to obtain complete witnesses (without witness-vars)
applySubst :: [(:<)] -> [Constraint] -> [Constraint]
applySubst = undefined


solveSub :: Constraint -> [Constraint]
solveSub (Subtype _ Top) = []
solveSub (Subtype Bot _) = []
solveSub (Subtype t (Inter r s)) = [Subtype t r, Subtype t s]
solveSub (Subtype (Union t s) r) = [Subtype t r, Subtype t s]
solveSub (Subtype Nat Nat) = []
solveSub (Subtype Int' Int') = []
solveSub (Subtype Nat Int') = []
solveSub _ = error "no"

type SolverM a = StateT [Char] (WriterT [(:<)] (Except String)) a

runSolverM :: SolverM a -> Either String (a,[(:<)])
runSolverM s = runExcept $ runWriterT $ evalStateT s ['a'..]

solveSubWithWitness :: Constraint -> SolverM ([Constraint], (:<))
solveSubWithWitness (Subtype _ Top) = pure ([], FromTop)
solveSubWithWitness (Subtype Bot _) = pure ([], ToBot)
solveSubWithWitness (Subtype t (Inter r s)) = do
    foo <- get
    let (var1:(var2:rest)) = foo -- ???
    put rest
    pure ([InComplete var1 $ Subtype t r, InComplete var2 $ Subtype t s], Meet (SubVar var1) (SubVar var2))
solveSubWithWitness (Subtype (Union t s) r)  = do
    foo <- get
    let (var1:(var2:rest)) = foo -- ???
    put rest
    pure ([InComplete var1 $ Subtype t r, InComplete var2 $ Subtype t s], Join (SubVar var1) (SubVar var2))
solveSubWithWitness (Subtype Nat Nat) = pure ([], Refl)
solveSubWithWitness (Subtype Int' Int') = pure ([], Refl)
solveSubWithWitness (Subtype Nat Int') = pure ([], Prim)
solveSubWithWitness _ = throwError "no"

data Dictionary t where
    ShowDict :: Dictionary t
    DefDict  :: Dictionary t

-- data Witness t where
--     CoV      :: Dictionary t -> s :< t -> Witness s
--     ContraV  :: Dictionary t -> t :< s -> Witness s

