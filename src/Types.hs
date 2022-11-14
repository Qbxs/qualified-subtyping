module Types where


newtype RecVar = MkRecVar { unRecVar :: String }
 deriving (Show, Eq, Ord)

newtype UniVar = MkUniVar { unUniVar :: String }
 deriving (Show, Eq, Ord)

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