{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Witnesses
    ( generateWitnesses
    , reconstruct
    , Constraint(..)
    , Typ(..)
    , Witness
    , RecVar(..)
    , UniVar(..)
    ) where

import           Control.Monad.Except
import           Control.Monad.State

import           Control.Monad.Reader
import           Data.Map                       ( Map )
import qualified Data.Map                      as M
import           Data.Set                       ( Set )
import qualified Data.Set                      as S
import           Text.Show.Pretty               ( ppShow )


-- | Reconstruct a constraint from a subtyping witness
--   for showing that constraints are isomorphic to their witnesses.
-- Inverse of /solve/.
reconstruct :: Witness -> Constraint
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
    let (Subtype t' t) = reconstruct w1
        (Subtype s s') = reconstruct w2
    in  Subtype (FuncTy t s) (FuncTy t' s')
reconstruct Prim = Subtype Nat Int'
reconstruct (UnfoldL recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype (RecTy recVar t) s
reconstruct (UnfoldR recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype t (RecTy recVar s)
reconstruct (LookupL recVar w) =
    let (Subtype _t s) = reconstruct w
    in Subtype (RecVar recVar) s
reconstruct (LookupR recVar w) =
    let (Subtype t _s) = reconstruct w
    in Subtype t (RecVar recVar)
reconstruct (UniVarB uv1 uv2) = Subtype (UniVar uv1) (UniVar uv2)
reconstruct (UniVarL uv ub) = Subtype (UniVar uv) ub
reconstruct (UniVarR uv lb) = Subtype lb (UniVar uv)
reconstruct (Fix c) = c
reconstruct SubVar{} = error "subvar should not occur"

type SolverM = StateT SolverState (Except String)

newtype RecVar = MkRecVar { unRecVar :: String }
 deriving (Show, Eq, Ord)

newtype UniVar = MkUniVar { unUniVar :: String }
 deriving (Show, Eq, Ord)

data SolverState = SolverState
    { ss_cache :: Map Constraint Witness
     -- ^ already solved constraints
    , ss_vars  :: Map UniVar VarState
      -- ^ mapping from UniVars to their bounds
    } deriving Show

data VarState = VarState
    { vs_upperbounds :: [Typ]
    , vs_lowerbounds :: [Typ]
    } deriving Show

runSolverM :: SolverM a -> Either String SolverState
runSolverM s = snd <$> runExcept (runStateT s (SolverState M.empty (M.singleton (MkUniVar "u0") (VarState [] []))))

-- | Generate subtyping witnesses for subtyping constraints.
generateWitnesses :: [Constraint] -> Either String (Map Constraint Witness)
generateWitnesses cs = ss_cache <$> runSolverM (solve (toDelayed <$> cs) >> runReaderT substitute S.empty)

data Typ where
    Top    :: Typ
    Bot    :: Typ
    Inter  :: Typ -> Typ -> Typ
    Union  :: Typ -> Typ -> Typ
    FuncTy :: Typ -> Typ -> Typ
    Int'   :: Typ
    Nat    :: Typ
    UniVar :: UniVar -> Typ
    RecVar :: RecVar -> Typ
    RecTy  :: RecVar -> Typ -> Typ
 deriving (Show, Eq, Ord)

data Witness where
    Refl    :: Typ -> Witness
    FromTop :: Typ -> Witness
    ToBot   :: Typ -> Witness
    Meet    :: Witness -> Witness -> Witness
    Join    :: Witness -> Witness -> Witness
    Func    :: Witness -> Witness -> Witness
    Prim    :: Witness
    UnfoldL :: RecVar -> Witness -> Witness
    UnfoldR :: RecVar -> Witness -> Witness
    LookupL :: RecVar -> Witness -> Witness
    LookupR :: RecVar -> Witness -> Witness
    UniVarL :: UniVar -> Typ -> Witness
    UniVarR :: UniVar -> Typ -> Witness
    UniVarB :: UniVar -> UniVar -> Witness
    -- | only used during witness generation
    SubVar  :: DelayedConstraint -> Witness
    Fix     :: Constraint -> Witness
 deriving Show

data Constraint where
    Subtype :: Typ -> Typ -> Constraint
 deriving (Show, Eq, Ord)

data DelayedConstraint where
    Delayed :: Typ -> Map RecVar Typ
            -> Typ -> Map RecVar Typ
            -> DelayedConstraint
 deriving (Show, Eq, Ord)

toDelayed :: Constraint -> DelayedConstraint
toDelayed (Subtype t s) = Delayed t M.empty s M.empty

fromDelayed :: DelayedConstraint -> Constraint
fromDelayed (Delayed t _ s _) = Subtype t s

-- | Solve constraints, and write corresponding witnesses in cache.
solve :: [DelayedConstraint] -> SolverM ()
solve [] = pure ()
solve (c : css) = do
    cacheHit <- inCache (fromDelayed c)
    if cacheHit then solve css else
      case c of
        (Delayed (UniVar uvl) m tvu@(UniVar uvu) m') ->
          if uvl == uvu
          then addToCache (fromDelayed c) (UniVarB uvl uvl) >> solve css
          else do
            newCss <- addUpperBounds uvl tvu m m'
            addToCache (fromDelayed c) (UniVarB uvl uvu)
            solve (newCss ++ css)
        (Delayed (UniVar uv) m ub m') -> do
          newCss <- addUpperBounds uv ub m m'
          addToCache (fromDelayed c) (UniVarL uv ub)
          solve (newCss ++ css)
        (Delayed lb m (UniVar uv) m') -> do
          newCss <- addLowerBounds uv lb m m'
          addToCache (fromDelayed c) (UniVarR uv lb)
          solve (newCss ++ css)
        _otherwise -> do
          (w, cs) <- solveSub c
          addToCache (fromDelayed c) w
          solve (cs ++ css)


-- | Substitute known witnesses for generated witness variables.
substitute :: ReaderT (Set DelayedConstraint) SolverM ()
substitute = do
    cache <- gets ss_cache
    forM_ (M.toList cache) $ \(c,w) -> do
      w <- go cache w
      modify $ \(SolverState cache' vars)
              -> SolverState (M.adjust (const w) c cache') vars
  where
    go :: Map Constraint Witness -> Witness -> ReaderT (Set DelayedConstraint) SolverM Witness
    go _ (Refl ty) = pure (Refl ty)
    go _ (FromTop ty) = pure (FromTop ty)
    go _ (ToBot ty) = pure (ToBot ty)
    go m (Meet w1 w2) = Meet <$> go m w1 <*> go m w2
    go m (Join w1 w2) = Join <$> go m w1 <*> go m w2
    go m (Func w1 w2) = Func <$> go m w1 <*> go m w2
    go _ Prim = pure Prim
    go m (UnfoldL recVar w) = UnfoldL recVar <$> go m w
    go m (UnfoldR recVar w) = UnfoldR recVar <$> go m w
    go m (LookupL recVar w) = LookupL recVar <$> go m w
    go m (LookupR recVar w) = LookupR recVar <$> go m w
    go _ (Fix c) = pure (Fix c)
    go _ (UniVarB uv1 uv2) = pure (UniVarB uv1 uv2)
    go _ (UniVarL uv ub) = pure (UniVarL uv ub)
    go _ (UniVarR uv lb) = pure (UniVarR uv lb)
    go m (SubVar c) = case M.lookup (fromDelayed c) m of
         Nothing -> throwError $ "Cannot find constraint: " <> show c <> " in env: " <> ppShow m
         Just (SubVar c') -> throwError "Tried to subtitute a variable with another variable"
         Just w -> asks (S.member c) >>= \case
            True -> pure $ Fix (fromDelayed c)
            False -> local (S.insert c) (go m w)


-- | Generate potentially incomplete witnesses
-- using fresh witness variables in place for branches
-- which will be substituted in later.
solveSub :: DelayedConstraint -> SolverM (Witness, [DelayedConstraint])
-- here we have to check whether the subconstraint is in cache
-- if it is, we have to put in /Fix/ with the constraint
-- otherwise we have cyclic references in /substitute/
solveSub (Delayed (RecVar recVar) m ty' m') = do
    case M.lookup recVar m of
        Nothing -> throwError $ "ƒailed lookupL for " ++ show recVar ++ ppShow m
        Just ty -> do
            let c = Delayed ty m ty' m'
            pure (LookupL recVar (SubVar c), [c])
solveSub (Delayed ty m (RecVar recVar) m') = do
    case M.lookup recVar m' of
        Nothing  -> throwError $ "ƒailed lookupR for " ++ show recVar ++ ppShow m'
        Just ty' -> do
            let c = Delayed ty m ty' m'
            pure (LookupR recVar (SubVar c), [c])
solveSub (Delayed rc@(RecTy recVar ty) m ty' m') = do
    let c = Delayed ty (M.insert recVar rc m) ty' m'
    pure (UnfoldL recVar (SubVar c), [c])
solveSub (Delayed ty m rc@(RecTy recVar ty') m') = do
    let c = Delayed ty m ty' (M.insert recVar rc m')
    pure (UnfoldR recVar (SubVar c), [c])
solveSub (Delayed (FuncTy t s) m (FuncTy t' s') m') = do
    let c1 = Delayed t' m t m'
    let c2 = Delayed s m s' m'
    pure (Func (SubVar c1) (SubVar c2), [c1, c2])
solveSub (Delayed t m (Inter r s) m') = do
    let c1 = Delayed t m r m'
    let c2 = Delayed t m s m'
    pure (Meet (SubVar c1) (SubVar c2), [c1, c2])
solveSub (Delayed (Union t s) m r m') = do
    let c1 = Delayed t m r m'
    let c2 = Delayed s m r m'
    pure (Join (SubVar c1) (SubVar c2), [c1, c2])
solveSub (fromDelayed -> Subtype ty  Top) = pure (FromTop ty, [])
solveSub (fromDelayed -> Subtype Bot ty) = pure (ToBot ty, [])
solveSub (fromDelayed -> Subtype Nat  Nat) = pure (Refl Nat, [])
solveSub (fromDelayed -> Subtype Int' Int') = pure (Refl Int', [])
solveSub (fromDelayed -> Subtype Nat  Int') = pure (Prim, [])
solveSub c = throwError $ "Cannot solve constraint:\n" <> show c

-------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------

-- | Check whether constraint is already solved.
inCache :: Constraint -> SolverM Bool
inCache c =  gets $ M.member c . ss_cache

-- | Add solved constraint to cache and known witnesses.
addToCache :: Constraint -> Witness -> SolverM ()
addToCache c w = modify $ \(SolverState cache vars) -> SolverState (M.insert c w cache) vars

modifyBounds :: (VarState -> VarState) -> UniVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState cache vars) -> SolverState cache (M.adjust f uv vars))

-- | Get the variable state from the state for a univar.
getBounds :: UniVar -> SolverM VarState
getBounds uv = do
  bounds <- gets ss_vars
  case M.lookup uv bounds of
    Nothing -> throwError $ "Tried to retrieve bounds for variable:" ++ unUniVar uv
    Just vs -> return vs

-- | Add type to lower bounds of a univar and generate new constraints based on the upper bounds.
addLowerBounds :: UniVar -> Typ -> Map RecVar Typ -> Map RecVar Typ -> SolverM [DelayedConstraint]
addLowerBounds uv ty m m' = do
  modifyBounds (\(VarState ubs lbs) -> VarState ubs (ty:lbs)) uv
  bounds <- getBounds uv
  let ubs = vs_upperbounds bounds
  return [Delayed ty m ub m' | ub <- ubs]

-- | Add type to upper bounds of a univar and generate new constraints based on the lower bounds.
addUpperBounds :: UniVar -> Typ -> Map RecVar Typ -> Map RecVar Typ -> SolverM [DelayedConstraint]
addUpperBounds uv ty m m' = do
  modifyBounds (\(VarState ubs lbs) -> VarState (ty:ubs) lbs) uv
  bounds <- getBounds uv
  let lbs = vs_lowerbounds bounds
  return [Delayed lb m ty m' | lb <- lbs]
