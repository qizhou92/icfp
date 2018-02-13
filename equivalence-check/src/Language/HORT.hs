module Language.HORT where
-- Higher Order Refinement Types

import Data.Data (Data)
import Data.Tree

import Grammar

newtype HORT = HORT { getHORT :: Tree Nonterminal }
  deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype :: HORT -> HORT -> [Rule]
subtype = undefined
