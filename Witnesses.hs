{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StrictData #-}

module Witnesses
    ( main
    , generateWitnesses
    ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                       ( Map )
import qualified Data.Map                      as M
import           Data.Tuple                     ( swap )

main :: IO ()
main =
    case
            generateWitnesses
                [ Subtype Bot Top
                , Subtype Nat (Inter (Inter Top Nat) Int')
                , Subtype (Union Int' (Union Nat Bot)) Int'
                , Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int')
                , Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) Top
                ]
        of
            Left  err -> putStrLn err
            Right sol -> print sol

reconstruct :: (:<) -> Constraint
reconstruct (Refl    ty) = Subtype ty ty
reconstruct (FromTop ty) = Subtype ty Top
reconstruct (ToBot   ty) = Subtype Bot ty
reconstruct (Meet w1 w2) =
    let (Subtype t s) = reconstruct w1
        (Subtype r v) = reconstruct w2
    in  if t /= r
            then error ("Different subtypes: " <> show t <> " and " <> show r)
            else Subtype t (Inter s v)
reconstruct (Join w1 w2) =
    let (Subtype t s) = reconstruct w1
        (Subtype r v) = reconstruct w2
    in  if s /= v
            then error ("Different supertypes: " <> show s <> " and " <> show v)
            else Subtype (Union t r) s
reconstruct (Func w1 w2) =
    let (Subtype t s) = reconstruct w1
        (Subtype r v) = reconstruct w2
    in  Subtype (FuncTy r t) (FuncTy s v)
reconstruct Prim = Subtype Nat Int'
reconstruct (Rec w) =
    let (Subtype t s) = reconstruct w in error "rec cannot be reconstructed yet"
reconstruct SubVar{} = error "subvar should not occur"

type SolverM a = StateT SolverState (Except String) a

type Var = Char
data SolverState = SolverState
    { ss_cache :: Map Constraint Var
     -- ^ already solved constraints, indirectly points to subtyping witnesses via ss_known
    , ss_todos :: Map Var Constraint
    , -- ^ mapping from witness-var to constraint
      ss_known :: Map Var (:<)
    , -- ^ mapping from witness-var to witness
      ss_fresh :: [Var]
      -- ^ "stream" of fresh variables
    }
 deriving Show

runSolverM :: SolverM a -> Either String SolverState
runSolverM s = snd <$> runExcept (runStateT s (SolverState M.empty M.empty M.empty ['a' ..]))

-- | Generate subtyping witnesses for subtyping constraints.
generateWitnesses :: [Constraint] -> Either String (Map Constraint (:<))
generateWitnesses cs = verify =<< runSolverM (solve cs >> substitute)
  where
    verify (SolverState cache todos known _)
        | not (M.null todos) = Left ("Some todos are left:\n" <> show todos)
        | otherwise          = Right (M.compose known cache)

data Typ where
    Top    :: Typ
    Bot    :: Typ
    Inter  :: Typ -> Typ -> Typ
    Union  :: Typ -> Typ -> Typ
    FuncTy :: Typ -> Typ -> Typ
    Int'   :: Typ
    Nat    :: Typ
    -- UniVar :: String -> Typ
    RecVar :: String -> Typ
    RecTy  :: String -> Typ -> Typ
 deriving (Show, Eq, Ord)

data (:<) where
    Refl    :: Typ -> (:<)
    FromTop :: Typ -> (:<)
    ToBot   :: Typ -> (:<)
    Meet    :: (:<) -> (:<) -> (:<)
    Join    :: (:<) -> (:<) -> (:<)
    Func    :: (:<) -> (:<) -> (:<)
    Prim    :: (:<)
    -- VarW    :: (:<)
    Rec     :: (:<) -> (:<)
    -- | only used during witness generation
    SubVar  :: Var -> (:<)
 deriving Show

data Constraint where
    Subtype :: Typ -> Typ -> Constraint
 deriving (Show, Eq, Ord)

solve :: [Constraint] -> SolverM ()
solve [] = pure ()
solve (c : cs) = do
    cacheHit <- inCache c
    if cacheHit then solve cs else do
      w <- solveSubWithWitness c
      var <- freshVar
      addToCache c var w
      solveTodos
      solve cs

-- | Solve todos recursively.
solveTodos :: SolverM ()
solveTodos = do
    todos <- gets ss_todos
    known' <- mapM solveSubWithWitness todos
    modify $ \(SolverState cache todos' known fresh)
            -> SolverState cache (M.difference todos' todos) (M.union known' known) fresh
    unless (M.null todos) solveTodos

-- | Substitute known witnesses for generated witness variables.
substitute :: SolverM ()
substitute = do
    ws <- gets ss_known
    coalesced <- mapM (go ws) ws
    modify $ \(SolverState cache todos _ fresh)
            -> SolverState cache todos coalesced fresh
  where
    go :: Map Var (:<) -> (:<) -> SolverM (:<)
    go m (Refl ty) = pure (Refl ty)
    go m (FromTop ty) = pure (FromTop ty)
    go m (ToBot ty) = pure (ToBot ty)
    go m (Meet x0 x1) = Meet <$> go m x0 <*> go m x1
    go m (Join x0 x1) = Join <$> go m x0 <*> go m x1
    go m (Func x0 x1) = Func <$> go m x0 <*> go m x1
    go m Prim = pure Prim
    go m (Rec ty) = Rec <$> go m ty
    go m (SubVar c) = case M.lookup c m of
         Nothing -> throwError $ "Cannot find witness variable: " <> show c <> " in env: " <> show m
         Just (SubVar c') -> throwError "Tried to subtitute a variable with another variable"
         Just w -> go m w

-- | subconstraints for reference.
solveSub :: Constraint -> [Constraint]
solveSub (Subtype _ Top) = []
solveSub (Subtype Bot _) = []
solveSub (Subtype t (Inter r s)) = [Subtype t r, Subtype t s]
solveSub (Subtype (Union t s) r) = [Subtype t r, Subtype s r]
solveSub (Subtype (FuncTy t s) (FuncTy t' s')) = [Subtype t' t, Subtype s s']
solveSub (Subtype ty@RecTy{} ty') = [Subtype (unfoldRecType ty) ty']
solveSub (Subtype ty' ty@RecTy{}) = [Subtype ty' (unfoldRecType ty)]
solveSub (Subtype Nat Nat) = []
solveSub (Subtype Int' Int') = []
solveSub (Subtype Nat Int') = []
solveSub _ = error "Cannot solve constraint."

-- | Generate potentially incomplete witnesses
-- using fresh witness variables in place for branches
-- which will be substituted in later.
solveSubWithWitness :: Constraint -> SolverM (:<)
solveSubWithWitness (Subtype ty  Top        ) = pure (FromTop ty)
solveSubWithWitness (Subtype Bot ty         ) = pure (ToBot ty)
solveSubWithWitness (Subtype t   (Inter r s)) = do
    var1 <- freshVar
    var2 <- freshVar
    addTodos [(var1, Subtype t r), (var2, Subtype t s)]
    pure $ Meet (SubVar var1) (SubVar var2)
solveSubWithWitness (Subtype (Union t s) r) = do
    var1 <- freshVar
    var2 <- freshVar
    addTodos [(var1, Subtype t r), (var2, Subtype s r)]
    pure $ Join (SubVar var1) (SubVar var2)
solveSubWithWitness (Subtype ty@(RecTy _ _) ty') = do
    var <- freshVar
    addTodos [(var, Subtype (unfoldRecType ty) ty')]
    pure (Rec (SubVar var))
solveSubWithWitness (Subtype ty' ty@(RecTy _ _)) = do
    var <- freshVar
    addTodos [(var, Subtype ty' (unfoldRecType ty))]
    pure (Rec (SubVar var))
solveSubWithWitness (Subtype (FuncTy t s) (FuncTy t' s')) = do
    var1 <- freshVar
    var2 <- freshVar
    addTodos [(var1, Subtype t' t), (var2, Subtype s s')]
    pure $ Func (SubVar var1) (SubVar var2)
solveSubWithWitness (Subtype Nat  Nat ) = pure (Refl Nat)
solveSubWithWitness (Subtype Int' Int') = pure (Refl Int')
solveSubWithWitness (Subtype Nat  Int') = pure Prim
solveSubWithWitness c                   = throwError $ "Cannot solve constraint:\n" <> show c

-------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------

-- | Get fresh witness variable.
freshVar :: SolverM Var
freshVar = do
    stream <- gets ss_fresh
    let (var : rest) = stream
    modify $ \(SolverState cache todos known _)
            -> SolverState cache todos known rest
    pure var

-- | Add elements to todo-map.
addTodos :: [(Var, Constraint)] -> SolverM ()
addTodos new = modify $ \(SolverState cache todos known fresh) -> SolverState
    (M.union (M.fromList (swap <$> new)) cache)
    (M.union (M.fromList new) todos)
    known
    fresh

-- | Check whether constraint is already solved.
inCache :: Constraint -> SolverM Bool
inCache c =  gets $ M.member c . ss_cache

-- | Add solved constraint to cache and known witnesses.
addToCache :: Constraint -> Var -> (:<) -> SolverM ()
addToCache c var w = modify $ \(SolverState cache todos known fresh) -> SolverState
    (M.insert c var cache)
    todos
    (M.insert var w known)
    fresh

unfoldRecType :: Typ -> Typ
unfoldRecType rc@(RecTy var ty) = substituteRecVar var rc ty
unfoldRecType ty = ty

substituteRecVar :: String -> Typ -> Typ -> Typ
substituteRecVar var ty (RecVar var') | var == var' = ty
                                      | otherwise   = RecVar var'
substituteRecVar var ty (Inter t1 t2) =
    Inter (substituteRecVar var ty t1) (substituteRecVar var ty t2)
substituteRecVar var ty (Union t1 t2) =
    Union (substituteRecVar var ty t1) (substituteRecVar var ty t2)
substituteRecVar var ty (FuncTy t1 t2) =
    FuncTy (substituteRecVar var ty t1) (substituteRecVar var ty t2)
substituteRecVar var ty (RecTy var' ty') =
    RecTy var' (substituteRecVar var ty ty') -- WARNING: capture free substitution does not work
substituteRecVar _ _ ty' = ty'
