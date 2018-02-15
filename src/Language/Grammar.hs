module Language.Grammar where

import qualified Language.TypeInference as TI
import           Language.HOTypeInference
import           Language.Types

import           Grammar

-- | Given an expression, generate a grammar of type constraints which expresses
-- relationships between the types of subexpressions and the top level expression,
-- obeying the judgement rules of higher order refinement types.
exprGrammar :: CoreExpr -> Either InferenceError Grammar
exprGrammar e =
  case TI.typeCheck e of
    Left (TI.UnificationError t1 t2) -> Left (UnificationError t1 t2)
    Left (TI.UnboundError x) -> Left (UnboundError x)
    Right e' -> typeConstraints e'
