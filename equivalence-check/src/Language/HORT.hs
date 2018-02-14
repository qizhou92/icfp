module Language.HORT where
-- Higher Order Refinement Types

import Data.Data (Data)
import Data.Tree

import Grammar
import Formula hiding (Rule)

newtype HORT = HORT { getHORT :: Tree Nonterminal }
  deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype :: Category -> HORT -> HORT -> [Rule]
subtype category hort1 hort2 = buildSubType category (getHORT hort1) (getHORT hort2)

buildSubType :: Category -> (Tree Nonterminal) -> (Tree Nonterminal) -> [Rule]
buildSubType category (Node n1 subTrees1) (Node n2 subTrees2) = do
  let rule = Rule category n2 (LBool True) [n1]
  let rules = concat (zipWith (buildSubType category) subTrees2 subTrees1)
  rule:rules 
