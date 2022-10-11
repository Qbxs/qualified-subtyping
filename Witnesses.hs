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
import           Data.Tuple                     ( swap, uncurry )

main :: IO ()
main =
    case
            generateWitnesses
                [ Subtype Bot Top
                -- variable clash due to identical subconstraints
                -- , Subtype Nat (Inter Top Top)
                , Subtype Nat (Inter (Inter Top Nat) Int')
                , Subtype (Union Int' (Union Nat Bot)) Int'
                , Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int')
                -- not terminating example :(
                , Subtype (RecTy "a" (FuncTy Nat (RecVar "a")))
                          (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a"))))
                ]
        of
            Left  err -> error err
            Right sol -> do
                print sol
                putStrLn $ "Sanity test: " ++ show (M.mapWithKey (\k val -> reconstruct val == k) sol)

-- | Reconstruct a constraint from a subtyping witness
--   for showing that constraints are isomorphic to their witnesses.
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
    , ss_known :: Map Var (:<)
     -- ^ mapping from witness-var to witness
    , ss_fresh :: [Var]
      -- ^ "stream" of fresh variables
    }
 deriving Show

runSolverM :: SolverM a -> Either String SolverState
runSolverM s = snd <$> runExcept (runStateT s (SolverState M.empty M.empty ['a' ..]))

-- | Generate subtyping witnesses for subtyping constraints.
generateWitnesses :: [Constraint] -> Either String (Map Constraint (:<))
generateWitnesses cs = composeCache <$> runSolverM (solve cs >> substitute)
  where
    composeCache (SolverState cache known _) = M.compose known cache

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

-- | Solve constraints, and write corresponding witnesses in cache.
solve :: [Constraint] -> SolverM ()
solve [] = pure ()
solve (c : css) = do
    cacheHit <- inCache c
    if cacheHit then solve css else do
      var <- freshVar
      addToCache c var
      (w, cs) <- solveSubWithWitness c
      addToKnown var w
      mapM_ (uncurry solveWithVar) cs
      solve css

-- | Same as /solve/ but don't generate a new witness var.
--   Used for subwitnesses that have already a witness var assigned.
solveWithVar :: Var -> Constraint -> SolverM ()
solveWithVar var c = do
    cacheHit <- inCache c
    unless cacheHit $ do
      addToCache c var
      (w, cs) <- solveSubWithWitness c
      addToKnown var w
      mapM_ (uncurry solveWithVar) cs

-- | Substitute known witnesses for generated witness variables.
substitute :: SolverM ()
substitute = do
    ws <- gets ss_known
    coalesced <- mapM (go ws) ws
    modify $ \(SolverState todos _ fresh)
            -> SolverState todos coalesced fresh
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
solveSubWithWitness :: Constraint -> SolverM ((:<), [(Var, Constraint)])
solveSubWithWitness (Subtype ty  Top        ) = pure (FromTop ty, [])
solveSubWithWitness (Subtype Bot ty         ) = pure (ToBot ty, [])
solveSubWithWitness (Subtype t   (Inter r s)) = do
    c1@(var1, _) <- fromCacheOrFresh (Subtype t r)
    c2@(var2, _) <- fromCacheOrFresh (Subtype t s)
    pure (Meet (SubVar var1) (SubVar var2), catConstraints [c1, c2])
solveSubWithWitness (Subtype (Union t s) r) = do
    c1@(var1, _) <- fromCacheOrFresh (Subtype t r)
    c2@(var2, _) <- fromCacheOrFresh (Subtype s r)
    pure (Join (SubVar var1) (SubVar var2), catConstraints [c1, c2])
solveSubWithWitness (Subtype ty@(RecTy _ _) ty') = do
    -- cacheHit <- inCache (Subtype (unfoldRecType ty) ty')
    -- when cacheHit $ get >>= throwError . (++) (show (Subtype (unfoldRecType ty) ty')) . take 1000 . show
    c@(var, _) <- fromCacheOrFresh (Subtype (unfoldRecType ty) ty')
    pure (Rec (SubVar var), catConstraints [c])
solveSubWithWitness (Subtype ty' ty@(RecTy _ _)) = do
    -- cacheHit <- inCache (Subtype ty' (unfoldRecType ty))
    -- when cacheHit $ get >>= throwError . (++) (show (Subtype ty' (unfoldRecType ty))) . take 1000 . show
    c@(var, _) <- fromCacheOrFresh (Subtype ty' (unfoldRecType ty))
    pure (Rec (SubVar var), catConstraints [c])
solveSubWithWitness (Subtype (FuncTy t s) (FuncTy t' s')) = do
    c1@(var1, _) <- fromCacheOrFresh (Subtype t' t)
    c2@(var2, _) <- fromCacheOrFresh (Subtype s s')
    pure (Func (SubVar var1) (SubVar var2), catConstraints [c1, c2])
solveSubWithWitness (Subtype Nat  Nat ) = pure (Refl Nat, [])
solveSubWithWitness (Subtype Int' Int') = pure (Refl Int', [])
solveSubWithWitness (Subtype Nat  Int') = pure (Prim, [])
solveSubWithWitness c                   = throwError $ "Cannot solve constraint:\n" <> show c

-------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------

-- | Get fresh witness variable.
freshVar :: SolverM Var
freshVar = do
    stream <- gets ss_fresh
    let (var : rest) = stream
    modify $ \(SolverState todos known _)
            -> SolverState todos known rest
    pure var

-- | Get var for already solved constraint and /Nohting/
--   or generate new var and /Just/ constraint.
fromCacheOrFresh :: Constraint -> SolverM (Var, Maybe Constraint)
fromCacheOrFresh c = do
    cache <- gets ss_cache
    case M.lookup c cache of
        Nothing -> do
            newVar <- freshVar
            pure (newVar, Just c)
        Just var -> pure (var, Nothing)

-- | Collapse constraints
catConstraints :: [(Var, Maybe Constraint)] -> [(Var, Constraint)]
catConstraints [] = []
catConstraints ((var, Nothing):cs) = catConstraints cs
catConstraints ((var, Just c):cs) = (var, c) : catConstraints cs

-- | Check whether constraint is already solved.
inCache :: Constraint -> SolverM Bool
inCache c =  gets $ M.member c . ss_cache

-- | Add solved constraint to cache and known witnesses.
addToKnown :: Var -> (:<) -> SolverM ()
addToKnown var w = modify $ \(SolverState cache known fresh) -> SolverState
    cache
    (M.insert var w known)
    fresh

-- | Add solved constraint to cache and known witnesses.
addToCache :: Constraint -> Var -> SolverM ()
addToCache c var = modify $ \(SolverState cache known fresh) -> SolverState
    (M.insert c var cache)
    known
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
