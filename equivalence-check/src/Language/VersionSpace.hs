module Language.VersionSpace where

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Language.Types

type VersionSpace = VersionSpace' ()
newtype VersionSpace' a = VersionSpace { getVersionSpace :: Map (Type, Type) [VersionSpaceContent a] }
  deriving (Show, Read, Eq, Ord, Data)

data VersionSpaceContent a
  = Leaf a
  | Edge (Type, Type)
  deriving (Show, Read, Eq, Ord, Data)

emptyVersionSpace :: VersionSpace' a
emptyVersionSpace = VersionSpace M.empty

mkVersionSpace :: Type -> Type -> VersionSpace' (Type, Type)
mkVersionSpace t1 t2 = undefined
