module Language.VersionSpace where

import           Control.Monad.State

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Language.Types
import           Grammar

type VersionSpace = VersionSpace

emptyVersionSpace :: VersionSpace
emptyVersionSpace = VersionSpace
