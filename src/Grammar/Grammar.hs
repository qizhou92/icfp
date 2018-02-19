{-# LANGUAGE TemplateHaskell #-}
module Grammar.Grammar where

import           Control.Lens
import           Control.Monad.State

import           Data.Data.Lens
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc

import Formula hiding (Rule)

-- An identifier which should be completely unique per location.
type Symbol = Int

data Nonterminal = Nonterminal
  { _nonterminalSymbol :: Symbol
  , _nonterminalVars :: [Var]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Nonterminal

data Category = L | R
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Category where
  pretty = pretty . show

-- It is crucial that every variable in a nonterminal location over a rule is unique.
data Rule = Rule
  { _ruleCategory :: Category
  , _ruleBackwards :: Bool
  , _ruleLHS :: Nonterminal
  , _ruleBody :: Expr
  , _ruleRHS :: [Nonterminal]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Rule

data Grammar = Grammar
  { _grammarStart :: Symbol
  , _grammarRules :: [Rule]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Grammar

instance Pretty Grammar where
  pretty (Grammar start rs) = pretty start <> pretty "\n" <> vsep (map pretty rs)

-- An identifier which groups different instances of the same nonterminal location.
type ControlID = Int

instance Pretty Nonterminal where
  pretty (Nonterminal sym vs) = pretty sym <> pretty vs

instance Pretty Rule where
  pretty (Rule ct back lhs body rhs) =
    mconcat [ pretty ct
            , pretty back
            , pretty lhs
            , pretty ": "
            , pretty body
            , pretty " | "
            , pretty rhs ]

cardinality :: Symbol -> [Rule] -> Int
cardinality sym = length . filter (\r -> _nonterminalSymbol (_ruleLHS r) == sym)

instances :: [Rule] -> Set Symbol
instances = S.fromList . map (_nonterminalSymbol . _ruleLHS)

-- | Delete the rules for the instance.
delete :: Symbol -> [Rule] -> [Rule]
delete sym = filter (\r -> _nonterminalSymbol (_ruleLHS r) /= sym)

-- | Collect the rules whose nonterminal match the predicate.
rulesFor :: Symbol -> [Rule] -> [Rule]
rulesFor sym = filter (\r -> _nonterminalSymbol (_ruleLHS r) == sym)

rulesWith :: Symbol -> [Rule] -> [Rule]
rulesWith sym = filter (\r -> sym `elem` map (view nonterminalSymbol) (r ^. ruleRHS))

type Clones = [Set Symbol]

clone :: Symbol -> Symbol -> Clones -> Clones
clone i j (cs:css) = if i `elem` cs then S.insert j cs:css else cs:clone i j css
clone i j [] = [S.fromList [i, j]]

cloneFor :: Symbol -> Clones -> Set Symbol
cloneFor i (cs:css) = if i `elem` cs then cs else cloneFor i css
cloneFor i [] = S.singleton i

predecessors :: [Rule] -> Symbol -> Set Symbol
predecessors rs s =
  S.fromList $ concatMap (toListOf (ruleRHS . traverse . nonterminalSymbol)) (rulesFor s rs)

successors :: Grammar -> Symbol -> Set Symbol
successors g s =
  S.fromList $ map (view (ruleLHS . nonterminalSymbol)) (rulesWith s (g ^. grammarRules))

visit :: MonadState (Set Symbol) m => a -> (Symbol -> m a) -> Symbol -> m a
visit def f sym = do
  visited <- get
  if sym `elem` visited
  then pure def
  else modify (S.insert sym) >> f sym

descendants :: Grammar -> Symbol -> Set Symbol
descendants g s = evalState (desc s) S.empty
  where
    desc = visit S.empty (\sym -> do
      let ss = successors g sym
      ss' <- mapM desc (S.toList ss)
      return (S.unions $ ss : ss'))

nonterminals :: (Applicative f, Data a) => (Nonterminal -> f Nonterminal) -> a -> f a
nonterminals = biplate

allSymbols :: (Applicative f, Data a) => (Symbol -> f Symbol) -> a -> f a
allSymbols = biplate

symbols :: Data a => a -> Set Symbol
symbols = S.fromList . toListOf allSymbols

categorize :: [Rule] -> Map Category [Rule]
categorize = foldr (\r -> M.insertWith (++) (r ^. ruleCategory) [r]) M.empty

lhsSymbol :: Rule -> Symbol
lhsSymbol = view (ruleLHS . nonterminalSymbol)

rhsSymbols :: Rule -> Set Symbol
rhsSymbols = S.fromList . toListOf (ruleRHS . traverse . nonterminalSymbol)
