module Language.HORT where

import           Control.Monad.State
import           Data.Data (Data)
import           Data.Tree

import           Language.Types
import           Grammar
import qualified Formula as F

newtype HORT = HORT { getHORT :: Tree Nonterminal }
  deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype :: HORT -> HORT -> [Rule]
subtype = undefined

buildSubType :: Category -> Tree Nonterminal -> Tree Nonterminal -> [Rule]
buildSubType category (Node n1 subTrees1) (Node n2 subTrees2) = do
  let rule = Rule category n2 (F.LBool True) [n1]
  let rules = concat (zipWith (buildSubType category) subTrees2 subTrees1)
  rule:rules 

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the value of the expression.
valueOf :: HORT -> F.Expr
valueOf = undefined

-- | Whether or not this type is primitive.
isPrim :: HORT -> Bool
isPrim = undefined

-- | Given a list of free variables and a basic type, construct
-- a higher order refinement type.
fresh :: MonadState Int m => [F.Var] -> Type -> m HORT
fresh = undefined

-- | Split a refinement type at the arrow position.
split :: HORT -> Maybe (HORT, HORT)
split = undefined

-- | Generate a set of rules which constrain the higher order refinement types
-- by the given formula.
constrain :: HORT -> [HORT] -> F.Expr -> [Rule]
constrain head body constraint = undefined
  -- TODO constrain the shared free variables
  -- TODO construct grammar rule(s?)
