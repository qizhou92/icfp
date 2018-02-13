module Language.VersionSpace where

import           Control.Monad.State
import           Control.Monad.Except

import           Language.Types

import qualified Formula as F
import           Grammar

newtype Constraint = Constraint { getConstraint :: [(Symbol, [F.Type])] }
  deriving (Show, Read, Eq, Ord)

data VersionSpace = VersionSpace
emptyVersionSpace :: VersionSpace
emptyVersionSpace = VersionSpace

data Error
  = BadConstraint Constraint Type
  | ConstraintMismatch Constrain Constrain
  deriving (Show, Read, Eq, Ord)

type GrammarGen a = StateT Symbol (Either Error) a

translate :: CoreExpr -> Either Error Grammar
translate e = evalStateT (do
  c <- mkConstraint e
  go c e
  pure undefined) 0
  where
    go :: Constraint -> CoreExpr -> GrammarGen [Rule]
    go c = \case
      EApp applicand argument -> do
        appC <- mkConstraint applicand
        argC <- mkConstraint argument
        rsApp <- go appC applicand
        rsArg <- go argC argument
        rsOut <- constrainOutput c appC
        pure (rsApp ++ rsArg)

      EInt i -> case c of
        Constraint [(s, [F.Int])] ->
          let v = F.Var "x" F.Int in
          pure [Rule L (Production s [v]) (F.mkEql F.Int (F.LInt (toInteger i)) (F.V v)) []]
        _ -> throwError (BadConstraint c TInt)

      EBool b -> case c of
        Constraint [(s, [F.Bool])] ->
          let v = F.Var "x" F.Bool in
          pure [Rule L (Production s [v]) (F.mkEql F.Bool (F.LBool b) (F.V v)) []]
        _ -> throwError (BadConstraint c TBool)

mkConstraint :: CoreExpr -> GrammarGen Constraint
mkConstraint = undefined

constrainOutput :: Constraint -> Constraint -> GrammarGen [Rule]
constrainOutput constraint toConstrain =
  undefined

