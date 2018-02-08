module Language.VersionSpace where

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Language.Types

newtype VersionSpace = VersionSpace { getVersionSpace :: Map (Type, Type) [(Type, Type)] }
  deriving (Show, Read, Eq, Ord, Data)

emptyVersionSpace :: VersionSpace
emptyVersionSpace = VersionSpace M.empty

mkVersionSpace :: Type -> Type -> VersionSpace
mkVersionSpace = undefined
