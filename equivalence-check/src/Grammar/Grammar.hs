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

import Formula hiding (Production)

class Symbol s where
  generate :: s -> String
  interpret :: String -> s

instance Symbol Int where
  generate = show
  interpret = read

data Nonterminal sym = Nonterminal
  { _nonterminalSymbol :: sym
  , _nonterminalVars :: [Var]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Nonterminal

data Category = L | R
  deriving (Show, Read, Eq, Ord, Data)

instance Pretty Category where
  pretty = pretty . show

-- It is crucial that every variable in a nonterminal location over a production is unique.
data Production sym = Production
  { _productionCategory :: Category
  , _productionLHS :: Nonterminal sym
  , _productionBody :: Expr
  , _productionRHS :: [Nonterminal sym]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Production

data Grammar sym = Grammar
  { _grammarStart :: sym
  , _grammarProductions :: [Production sym]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Grammar

instance Pretty sym => Pretty (Grammar sym) where
  pretty (Grammar start rs) = pretty start <> pretty "\n" <> vsep (map pretty rs)

-- An identifier which groups different instances of the same nonterminal location.
type ControlID = Int

instance Pretty sym => Pretty (Nonterminal sym) where
  pretty (Nonterminal sym vs) = pretty sym <> pretty vs

instance Pretty sym => Pretty (Production sym) where
  pretty (Production ct lhs body rhs) =
    mconcat [ pretty ct
            , pretty lhs
            , pretty ": "
            , pretty body
            , pretty " | "
            , pretty rhs ]

cardinality :: Eq sym => sym -> [Production sym] -> Int
cardinality sym = length . filter (\r -> _nonterminalSymbol (_productionLHS r) == sym)

instances :: Ord sym => [Production sym] -> Set sym
instances = S.fromList . map (_nonterminalSymbol . _productionLHS)

-- | Delete the productions for the instance.
delete :: Ord sym => sym -> [Production sym] -> [Production sym]
delete sym = filter (\r -> _nonterminalSymbol (_productionLHS r) /= sym)

-- | Collect the productions whose nonterminal match the predicate.
productionsFor :: Ord sym => sym -> [Production sym] -> [Production sym]
productionsFor sym = filter (\r -> _nonterminalSymbol (_productionLHS r) == sym)

productionsWith :: Ord sym => sym -> [Production sym] -> [Production sym]
productionsWith sym = filter (\r -> sym `elem` map (view nonterminalSymbol) (r ^. productionRHS))

type Clones sym = [Set sym]

clone :: Ord sym => sym -> sym -> Clones sym -> Clones sym
clone i j (cs:css) = if i `elem` cs then S.insert j cs:css else cs:clone i j css
clone i j [] = [S.fromList [i, j]]

cloneFor :: Ord sym => sym -> Clones sym -> Set sym
cloneFor i (cs:css) = if i `elem` cs then cs else cloneFor i css
cloneFor i [] = S.singleton i

predecessors :: Ord sym => [Production sym] -> sym -> Set sym
predecessors rs s =
  S.fromList $ concatMap (toListOf (productionRHS . traverse . nonterminalSymbol)) (productionsFor s rs)

successors :: Ord sym => Grammar sym -> sym -> Set sym
successors g s =
  S.fromList $ map (view (productionLHS . nonterminalSymbol)) (productionsWith s (g ^. grammarProductions))

visit :: (Ord sym, MonadState (Set sym) m) => a -> (sym -> m a) -> sym -> m a
visit def f sym = do
  visited <- get
  if sym `elem` visited
  then pure def
  else modify (S.insert sym) >> f sym

descendants :: Ord sym => Grammar sym -> sym -> Set sym
descendants g s = evalState (desc s) S.empty
  where
    desc = visit S.empty (\sym -> do
      let ss = successors g sym
      ss' <- mapM desc (S.toList ss)
      return (S.unions $ ss : ss'))

nonterminals :: (Data sym, Applicative f, Data a) => (Nonterminal sym -> f (Nonterminal sym)) -> a -> f a
nonterminals = biplate

allSymbols :: (Applicative f, Data a, Data sym) => (sym -> f sym) -> a -> f a
allSymbols = biplate

symbols :: (Data a, Data sym, Ord sym) => a -> Set sym
symbols = S.fromList . toListOf allSymbols

categorize :: [Production sym] -> Map Category [Production sym]
categorize = foldr (\r -> M.insertWith (++) (r ^. productionCategory) [r]) M.empty

lhsSymbol :: Production sym -> sym
lhsSymbol = view (productionLHS . nonterminalSymbol)

rhsSymbols :: Ord sym => Production sym -> Set sym
rhsSymbols = S.fromList . toListOf (productionRHS . traverse . nonterminalSymbol)
