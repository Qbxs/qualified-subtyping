{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Witnesses
    ( generateWitnesses
    -- , reconstruct
    , Constraint(..)
    , Typ(..)
    , (:<)
    , RecVar(..)
    , UniVar(..)
    ) where

import           Control.Monad.Except
import           Control.Monad.State
import           GHC.Base                       ( Alternative(..) )
import           Data.Map                       ( Map )
import qualified Data.Map                      as M
import           Data.Set                       ( Set )
import qualified Data.Set                      as S
import           Data.Tuple                     ( swap, uncurry )
import           Data.Maybe                     ( fromMaybe )
import           Text.Show.Pretty               ( ppShow )

{-
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
    let (Subtype t' t) = reconstruct w1
        (Subtype s s') = reconstruct w2
    in  Subtype (FuncTy t s) (FuncTy t' s')
reconstruct Prim = Subtype Nat Int'
reconstruct (UnfoldL wVar recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype (fromMaybe (error $ "no rectype found in " ++ show t) (getRecType recVar t)) s
reconstruct (UnfoldR wVar recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype t (fromMaybe (error $ "no rectype found in " ++ show s) (getRecType recVar s))
reconstruct (Fix c) = c
reconstruct SubVar{} = error "subvar should not occur"
-}

type SolverM = StateT SolverState (Except String)

type Var = Char

newtype RecVar = MkRecVar { unRecVar :: String }
 deriving (Show, Eq, Ord)

newtype UniVar = MkUniVar { unUniVar :: String }
 deriving (Show, Eq, Ord)
data SolverState = SolverState
    { ss_cache :: Map Constraint (:<)
     -- ^ already solved constraints
    , ss_fresh :: [Var]
      -- ^ "stream" of fresh variables
    , ss_vars  :: Map UniVar VarState
      -- ^ mapping from UniVars to their bounds
    } deriving Show

data VarState = VarState
    { vs_upperbounds :: [Typ]
    , vs_lowerbounds :: [Typ]
    } deriving Show

runSolverM :: SolverM a -> Either String SolverState
runSolverM s = snd <$> runExcept (runStateT s (SolverState M.empty ['a' ..] (M.singleton (MkUniVar "u0") (VarState [] []))))

-- | Generate subtyping witnesses for subtyping constraints.
generateWitnesses :: [Constraint] -> Either String (Map Constraint (:<))
generateWitnesses cs = ss_cache <$> runSolverM (solve (toDelayed <$> cs) >> evalStateT substitute S.empty)

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

data (:<) where
    Refl    :: Typ -> (:<)
    FromTop :: Typ -> (:<)
    ToBot   :: Typ -> (:<)
    Meet    :: (:<) -> (:<) -> (:<)
    Join    :: (:<) -> (:<) -> (:<)
    Func    :: (:<) -> (:<) -> (:<)
    Prim    :: (:<)
    UnfoldL :: Var -> RecVar -> (:<) -> (:<)
    UnfoldR :: Var -> RecVar -> (:<) -> (:<)
    LookupL :: RecVar -> (:<) -> (:<)
    LookupR :: RecVar -> (:<) -> (:<)
    -- | only used during witness generation
    SubVar  :: DelayedConstraint -> (:<)
    Fix     :: Constraint -> (:<)
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
        (fromDelayed -> Subtype (UniVar uvl) tvu@(UniVar uvu)) ->
          if uvl == uvu
          then solve css
          else do
            newCss <- addUpperBounds uvl tvu
            solve ((toDelayed <$> newCss) ++ css)
        (fromDelayed -> Subtype (UniVar uv) ub) -> do
          newCss <- addUpperBounds uv ub
          solve ((toDelayed <$> newCss) ++ css)
        (fromDelayed -> Subtype lb (UniVar uv)) -> do
          newCss <- addLowerBounds uv lb
          solve ((toDelayed <$> newCss) ++ css)
        _otherwise -> do
          (w, cs) <- solveSub c
          addToCache (fromDelayed c) w
          solve (cs ++ css)


-- | Substitute known witnesses for generated witness variables.
substitute :: StateT (Set Constraint) SolverM ()
substitute = do
    cache <- lift $ gets ss_cache
    x <- get
    coalesced <- mapM (go cache) cache
    lift $ modify $ \(SolverState _ fresh vars)
                   -> SolverState coalesced fresh vars
  where
    go :: MonadError String m => Map Constraint (:<) -> (:<) -> StateT (Set Constraint) m (:<)
    go m (Refl ty) = pure (Refl ty)
    go m (FromTop ty) = pure (FromTop ty)
    go m (ToBot ty) = pure (ToBot ty)
    go m (Meet w1 w2) = Meet <$> go m w1 <*> go m w2
    go m (Join w1 w2) = Join <$> go m w1 <*> go m w2
    go m (Func w1 w2) = Func <$> go m w1 <*> go m w2
    go m Prim = pure Prim
    go m (UnfoldL wVar recVar w) = UnfoldL wVar recVar <$> go m w
    go m (UnfoldR wVar recVar w) = UnfoldR wVar recVar <$> go m w
    go m (LookupL recVar w) = LookupL recVar <$> go m w
    go m (LookupR recVar w) = LookupR recVar <$> go m w
    go m (Fix c) = pure (Fix c)
    go m (SubVar c) = case M.lookup (fromDelayed c) m of
         Nothing -> throwError $ "Cannot find witness variable: " <> show c <> " in env: " <> ppShow m
         Just (SubVar c') -> throwError "Tried to subtitute a variable with another variable"
         Just w -> go m w -- do
            -- s <- get
            -- if S.member (fromDelayed c) s
            --     then pure $ Fix (fromDelayed c)
            --     else modify (S.insert (fromDelayed c)) >> go m w


-- | Generate potentially incomplete witnesses
-- using fresh witness variables in place for branches
-- which will be substituted in later.
solveSub :: DelayedConstraint -> SolverM ((:<), [DelayedConstraint])
solveSub (Delayed rc@(RecTy recVar ty) m ty' m') = do
    wVar <- freshVar
    let c = Delayed ty (M.insert recVar rc m) ty' m'
    pure (UnfoldL wVar recVar (SubVar c), [c])
solveSub (Delayed ty m rc@(RecTy recVar ty') m') = do
    wVar <- freshVar
    let c = Delayed ty m ty' (M.insert recVar rc m')
    pure (UnfoldR wVar recVar (SubVar c), [c])
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
solveSub (Delayed (RecVar recVar) m ty' m') = do
    case M.lookup recVar m of
        Nothing -> throwError $ "ƒailed lookupL for " ++ show recVar ++ ppShow m
        Just ty -> let c = Delayed ty m ty m' in pure (LookupL recVar (SubVar c), [c])
solveSub (Delayed ty m (RecVar recVar) m') = do
    case M.lookup recVar m' of
        Nothing  -> throwError $ "failed lookupR for " ++ show recVar ++ ppShow m'
        Just ty' -> let c = Delayed ty m ty' m' in pure (LookupR recVar (SubVar c), [c])
solveSub (fromDelayed -> Subtype ty  Top) = pure (FromTop ty, [])
solveSub (fromDelayed -> Subtype Bot ty) = pure (ToBot ty, [])
solveSub (fromDelayed -> Subtype Nat  Nat) = pure (Refl Nat, [])
solveSub (fromDelayed -> Subtype Int' Int') = pure (Refl Int', [])
solveSub (fromDelayed -> Subtype Nat  Int') = pure (Prim, [])
solveSub c = throwError $ "Cannot solve constraint:\n" <> show c

-------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------

-- | Get fresh witness variable.
freshVar :: SolverM Var
freshVar = do
    stream <- gets ss_fresh
    let (var : rest) = stream
    modify $ \(SolverState todos _ vars)
            -> SolverState todos rest vars
    pure var

-- | Check whether constraint is already solved.
inCache :: Constraint -> SolverM Bool
inCache c =  gets $ M.member c . ss_cache

-- | Add solved constraint to cache and known witnesses.
addToCache :: Constraint -> (:<) -> SolverM ()
addToCache c w = modify $ \(SolverState cache fresh vars) -> SolverState
    (M.insert c w cache)
    fresh
    vars

modifyBounds :: (VarState -> VarState) -> UniVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState cache fresh vars) -> SolverState cache fresh (M.adjust f uv vars))

getBounds :: UniVar -> SolverM VarState
getBounds uv = do
  bounds <- gets ss_vars
  case M.lookup uv bounds of
    Nothing -> throwError $ "Tried to retrieve bounds for variable:" ++ unUniVar uv
    Just vs -> return vs

addLowerBounds :: UniVar -> Typ -> SolverM [Constraint]
addLowerBounds uv ty = do
  modifyBounds (\(VarState ubs lbs) -> VarState ubs (ty:lbs)) uv
  bounds <- getBounds uv
  let ubs = vs_upperbounds bounds
  return [Subtype ty ub | ub <- ubs]

addUpperBounds :: UniVar -> Typ -> SolverM [Constraint]
addUpperBounds uv ty = do
  modifyBounds (\(VarState ubs lbs) -> VarState (ty:ubs) lbs) uv
  bounds <- getBounds uv
  let lbs = vs_lowerbounds bounds
  return [Subtype lb ty | lb <- lbs]