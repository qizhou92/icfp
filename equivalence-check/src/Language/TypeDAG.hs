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
  (BuildState visitedMap idN) <- get
  leftEdge <- buildLeftEdge coreExpr1 coreExpr2
  rightEdge <- buildRightEdge coreExpr1 coreExpr2
  allEdge <- buildAllEdge coreExpr1 coreExpr2
  put (BuildState visitedMap (idN+1))
  return (TypeDAGNode VersionSpace VersionSpace coreExpr1 coreExpr2 (leftEdge++rightEdge++allEdge) idN)

buildLeftEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildLeftEdge (EBin _ e1 e2) e = do
 subNode1 <- buildTypeDAG e1 e
 subNode2 <- buildTypeDAG e2 e
 return ([(TypeDAGEdge SL [subNode1,subNode2])])

buildLeftEdge (EIf e1 e2 e3) e = do
  subNode1 <- buildTypeDAG e1 e
  subNode2 <- buildTypeDAG e2 e
  subNode3 <- buildTypeDAG e3 e
  return ([(TypeDAGEdge SL [subNode1,subNode2,subNode3])])

buildLeftEdge (EApp e1 e2) e = do
  subNode1 <- buildTypeDAG e1 e
  subNode2 <- buildTypeDAG e2 e
  return ([(TypeDAGEdge SL [subNode1,subNode2])])

buildLeftEdge (ELam _ e1) e = do
  subNode1 <- buildTypeDAG e1 e
  return ([(TypeDAGEdge SL [subNode1])])

buildLeftEdge _ _ = return []

buildRightEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildRightEdge e (EBin _ e1 e2) = do
 subNode1 <- buildTypeDAG e e1
 subNode2 <- buildTypeDAG e e2
 return ([(TypeDAGEdge SR [subNode1,subNode2])])

buildRightEdge e (EIf e1 e2 e3) = do
  subNode1 <- buildTypeDAG e e1
  subNode2 <- buildTypeDAG e e2
  subNode3 <- buildTypeDAG e e3
  return ([(TypeDAGEdge SR [subNode1,subNode2,subNode3])])

buildRightEdge e (EApp e1 e2)  = do
  subNode1 <- buildTypeDAG e e1
  subNode2 <- buildTypeDAG e e2
  return ([(TypeDAGEdge SR [subNode1,subNode2])])

buildRightEdge e (ELam _ e1)  = do
  subNode1 <- buildTypeDAG e e1
  return ([(TypeDAGEdge SR [subNode1])])

buildRightEdge _ _ = return []

buildAllEdge :: CoreExpr -> CoreExpr -> (State BuildState) [TypeDAGEdge]
buildAllEdge (EMatch e1 e2 _ _ e3) (EMatch e4 e5 _ _ e6) = do
  subNode1 <- buildTypeDAG e1 e4
  subNode2 <- buildTypeDAG e2 e5
  subNode3 <- buildTypeDAG e3 e6
  return [(TypeDAGEdge SA [subNode1,subNode2,subNode3])]

buildAllEdge _ _ = return []