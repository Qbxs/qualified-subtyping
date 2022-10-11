{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StrictData #-}

module Witnesses
    ( main
    , generateWitnesses
    ) where

import           Control.Monad.Except
import           Control.Monad.State
import           GHC.Base                       ( Alternative(..) )
import           Data.Map                       ( Map )
import qualified Data.Map                      as M
import           Data.Tuple                     ( swap, uncurry )
import Data.Maybe (fromMaybe)

main :: IO ()
main =
    case
            generateWitnesses
                [ Subtype Bot Top
                , Subtype Nat (Inter Top Top)
                , Subtype Nat (Inter (Inter Top Nat) Int')
                , Subtype (Union Int' (Union Nat Bot)) Int'
                , Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int')
                , Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a"))))
                ]
        of
            Left  err -> error err
            Right sol -> do
                print sol
                let test = M.mapWithKey (\k val -> reconstruct val == k) sol
                putStrLn $ "Sanity test: " ++ show test
                putStrLn $ "All true? " ++ show (and $ M.elems test)

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
    in  Subtype (FuncTy s t) (FuncTy r v)
reconstruct Prim = Subtype Nat Int'
reconstruct (UnfoldL recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype t (fromMaybe (error $ "no rectype found in " ++ show s) (getRecType recVar s))
reconstruct (UnfoldR recVar w) =
    let (Subtype t s) = reconstruct w
    in  Subtype (fromMaybe (error $ "no rectype found in " ++ show t) (getRecType recVar t)) s
reconstruct (Fix c) = c
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
    UnfoldL :: String -> (:<) -> (:<)
    UnfoldR :: String -> (:<) -> (:<)
    Fix     :: Constraint -> (:<)
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
    go m (UnfoldL recVar ty) = UnfoldL recVar <$> go m ty
    go m (UnfoldR recVar ty) = UnfoldR recVar <$> go m ty
    go m (Fix ty) = pure (Fix ty)
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
    (c1@(var1, _), c2@(var2, _)) <- fromCacheOrFresh2 (Subtype t r) (Subtype t s)
    pure (Meet (SubVar var1) (SubVar var2), catConstraints [c1, c2])
solveSubWithWitness (Subtype (Union t s) r) = do
    (c1@(var1, _), c2@(var2, _)) <- fromCacheOrFresh2 (Subtype t r) (Subtype s r)
    pure (Join (SubVar var1) (SubVar var2), catConstraints [c1, c2])
solveSubWithWitness (Subtype ty@(RecTy recVar _) ty') = do
    let subc = Subtype (unfoldRecType ty) ty'
    cacheHit <- inCache subc
    if cacheHit then pure (Fix subc, []) else do
      c@(var, _) <- fromCacheOrFresh subc
      pure (UnfoldL recVar (SubVar var), catConstraints [c])
solveSubWithWitness (Subtype ty' ty@(RecTy recVar _)) = do
    let subc = Subtype ty' (unfoldRecType ty)
    cacheHit <- inCache subc
    if cacheHit then pure (Fix subc, []) else do
      c@(var, _) <- fromCacheOrFresh subc
      pure (UnfoldR recVar (SubVar var), catConstraints [c])
solveSubWithWitness (Subtype (FuncTy t s) (FuncTy t' s')) = do
    (c1@(var1, _), c2@(var2, _)) <- fromCacheOrFresh2 (Subtype t' t) (Subtype s s')
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

-- | Check constraints for equality in order not to generate witness vars for equal constraints.
fromCacheOrFresh2 :: Constraint -> Constraint -> SolverM ((Var, Maybe Constraint), (Var, Maybe Constraint))
fromCacheOrFresh2 c1 c2 | c1 == c2 = (\c -> (c,c)) <$> fromCacheOrFresh c1
                        | otherwise = do
                            c1 <- fromCacheOrFresh c1
                            c2 <- fromCacheOrFresh c2
                            pure (c1, c2)

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

-- | Unfold a recursive type once.
unfoldRecType :: Typ -> Typ
unfoldRecType rc@(RecTy var ty) = substituteRecVar var rc ty
unfoldRecType ty = ty

-- | Partial inverse of /unfoldRecType/.
getRecType :: String -> Typ -> Maybe Typ
getRecType varRec (FuncTy t1 t2) = getRecType varRec t1 <|> getRecType varRec t2
getRecType varRec (Union t1 t2) = getRecType varRec t1 <|> getRecType varRec t2
getRecType varRec (Inter t1 t2) = getRecType varRec t1 <|> getRecType varRec t2
getRecType varRec rc@(RecTy varRec' _) = if varRec == varRec' then pure rc else Nothing
getRecType varRec ty = Nothing

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

-- fromList [(Subtype Bot Top,FromTop Bot),(Subtype Bot Int',ToBot Int'),(Subtype (Union Int' (Union Nat Bot)) Int',Join (Refl Int') (Join Prim (ToBot Int'))),(Subtype (Union Nat Bot) Int',Join Prim (ToBot Int')),(Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int'),Func (Meet (FromTop Nat) Prim) Prim),(Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))),Func (Refl Nat) (UnfoldL "a" (Fix (Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))))))),(Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (RecTy "a" (FuncTy Nat (RecVar "a"))),Fix (Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))))),(Subtype Int' Int',Refl Int'),(Subtype Nat Top,FromTop Nat),(Subtype Nat (Inter Top Top),Meet (FromTop Nat) (FromTop Nat)),(Subtype Nat (Inter Top Int'),Meet (FromTop Nat) Prim),(Subtype Nat (Inter Top Nat),Meet (FromTop Nat) (Refl Nat)),(Subtype Nat (Inter (Inter Top Nat) Int'),Meet (Meet (FromTop Nat) (Refl Nat)) Prim),(Subtype Nat Int',Prim),(Subtype Nat Nat,Refl Nat),
-- (Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))),UnfoldL "a" (Func (Refl Nat) (UnfoldL "a" (Fix (Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))))))))
-- ,(Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (RecTy "a" (FuncTy Nat (RecVar "a"))),UnfoldL "a" (Fix (Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))))))]
-- Sanity test: fromList [(Subtype Bot Top,True),(Subtype Bot Int',True),(Subtype (Union Int' (Union Nat Bot)) Int',True),(Subtype (Union Nat Bot) Int',True),(Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int'),True),(Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))),False),(Subtype (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))) (RecTy "a" (FuncTy Nat (RecVar "a"))),False),(Subtype Int' Int',True),(Subtype Nat Top,True),(Subtype Nat (Inter Top Top),True),(Subtype Nat (Inter Top Int'),True),(Subtype Nat (Inter Top Nat),True),(Subtype Nat (Inter (Inter Top Nat) Int'),True),(Subtype Nat Int',True),(Subtype Nat Nat,True),(Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a")))),False),(Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (RecTy "a" (FuncTy Nat (RecVar "a"))),False)]
-- All true? False