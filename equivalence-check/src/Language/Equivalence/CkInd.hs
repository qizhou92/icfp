module Language.Equivalence.CkInd where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import Language.Equivalence.TypeInference
import qualified Data.Set as Set
import Language.Equivalence.Derivations
import qualified Language.Equivalence.Types as Types
import qualified Data.Map as Map
import Control.Monad.State

data CheckIndResult = CheckIndState (Map.Map [Der] Bool)
type CheckIndState a = StateT CheckIndResult IO a

checkInd ::  (Map.Map String Expr) ->(Set.Set [Der])-> [Der] ->CheckIndState Bool
checkInd invariants visited theDers = do
  (CheckIndState definedSet) <- get
  if Map.member theDers definedSet then return (Map.findWithDefault False theDers definedSet)
     else do
           result <- checkIndNewDers invariants theDers visited
           put (CheckIndState (Map.insert theDers result definedSet))
           return result


checkIndNewDers :: (Map.Map String Expr) -> [Der] ->(Set.Set [Der])->CheckIndState Bool
checkIndNewDers invariants location1 visited = do
  entailResult <- liftIO (checkByEntail invariants location1 visited)
  if entailResult then return True
    else do
          splitResult <- checkBySplit invariants location1 visited
          if splitResult then return True
            else checkByUnwind invariants location1 visited
    

checkByEntail :: (Map.Map String Expr) -> [Der] ->(Set.Set [Der])-> IO Bool
checkByEntail invariants location1 visitedSet = do
  let sameLocationList = Set.toList (Set.filter (isSameLocation location1) visitedSet)
  resultList <- mapM (isEntailHolds invariants location1) sameLocationList
  let list = takeWhile ( == False) resultList
  if length(list) == length(resultList) then return False
    else return True

-- this function need to re-implement, the order might not be right.
isEntailHolds :: (Map.Map String Expr) -> [Der] -> [Der] ->IO Bool
isEntailHolds invariants location1 location2 = do
  let predicateName1 = "R" ++ (foldr getPredicateName "" location1)
  let invariants1 = Map.findWithDefault (ExprConstant (ConstantBool False)) predicateName1 invariants
  let predicateName2 = "R" ++ (foldr getPredicateName "" location2)
  let invariants2 = Map.findWithDefault (ExprConstant (ConstantBool True)) predicateName2 invariants
  checkEntail invariants1 invariants2 

isSameLocation :: [Der] -> [Der] -> Bool
isSameLocation location1 location2 = do
  if length(location1) /= length(location2) then False
    else do
         let list = (zipWith isSameCoreExpr location1 location2)
         let result = takeWhile ( == True) list
         if length(result) == length(list) then True
            else False 

getPredicateName :: Der -> String -> String
getPredicateName der@(Der _ _ _ idNumber) oldName =
  (show idNumber) ++ "!" ++ oldName

isSameCoreExpr :: Der -> Der -> Bool
isSameCoreExpr der1@(Der _ expr1 _ _) der2@(Der _ expr2 _ _) = do
  if expr1 == expr2 then True
    else False

checkBySplit :: (Map.Map String Expr) -> [Der] ->(Set.Set [Der])->CheckIndState Bool
checkBySplit invariants location visited = do
  if length(location) < 2 then return False
    else do
         let allSplitLocation = splitLocation location
         let newVisited = Set.insert location visited
         result <- mapM (isPairInd invariants newVisited) allSplitLocation
         let list = takeWhile ( == False) result
         if length(list) == length(result) then return False
           else return True

isPairInd :: (Map.Map String Expr) -> (Set.Set [Der]) -> ([Der],[Der]) -> CheckIndState Bool
isPairInd invariants visited (location1,location2) = do
  result1 <- checkInd invariants visited location1
  result2 <- checkInd invariants visited location2 
  return (result1 && result2)

-- need to change if we allowe arbitrary split
splitLocation :: [Der] -> [([Der],[Der])]
splitLocation location = map  ( (\x y -> splitAt y x) location) [1 .. ((length location)-1)]
 
checkByUnwind :: (Map.Map String Expr) -> [Der] ->(Set.Set [Der])->CheckIndState Bool
checkByUnwind invariants location visited = do
 if (isRNSymbloc location) then False
   else do
         let allUnwindLocation = map (unwindByIndex location) [1 .. (length location)]
         let newVisited = Set.insert location visited
         result <- mapM (checkInd invariants newVisited) allUnwindLocation
         let list = takeWhile ( == False) result
         if length(list) == length(result) then return False
           else return True

isRNSymbloc :: [Der] -> Bool
isRNSymbloc (Der RASymb):[] = True
isRNSymbloc _ =False

unwindByIndex :: [Der] -> Int -> [Der]
unwindByIndex location index= do
  let prefix = take (index - 1) location
  let suffix = drop index location
  let (Der _ _ successor _) = location !! index
  prefix ++ successor ++ suffix


