module Language.TypeDAG where
import Language.Types
import Language.VersionSpace
import Control.Monad.State
import qualified Data.Map as Map

data BuildState = BuildState (Map.Map (CoreExpr,CoreExpr) TypeDAGNode) Int

-- TypeDAGNode Context RelationalType CoreExpr1 CoreExpr2 TypeDAGEdges UniqueId
data TypeDAGNode = TypeDAGNode VersionSpace VersionSpace CoreExpr CoreExpr [TypeDAGEdge] Int

-- TypeDAGEdge Symbol(Left,Right,All) 
data TypeDAGEdge = TypeDAGEdge Symbol [TypeDAGNode]

--Symbol L, R, A
data Symbol = SL | SR | SA

buildTypeDAG :: CoreExpr -> CoreExpr -> (State BuildState) TypeDAGNode
buildTypeDAG coreExpr1 coreExpr2 = do
  (BuildState visitedMap _) <- get
  if (Map.member (coreExpr1,coreExpr2) visitedMap) then return (visitedMap Map.! (coreExpr1,coreExpr2))
     else buildNewTypeNode coreExpr1 coreExpr2


buildNewTypeNode :: CoreExpr -> CoreExpr -> (State BuildState) TypeDAGNode
buildNewTypeNode coreExpr1 coreExpr2 = do
  (BuildState visitedMap id) <- get
  leftEdge <- buildLeftEdge coreExpr1 coreExpr2
  rightEdge <- buildRightEdge coreExpr1 coreExpr2
  allEdge <- buildAllEdge coreExpr1 coreExpr2
  put (BuildState visitedMap id+1)
  return (VersionSpace VersionSpace coreExpr1 coreExpr2 (leftEdge++rightEdge++allEdge) id)

buildLeftEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildLeftEdge = undefined

buildRightEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildRightEdge = undefined

buildAllEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildAllEdge = undefined