module Language.Equivalence.CkInd where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import Language.Equivalence.TypeInference
import qualified Data.Set as Set
import Language.Equivalence.Derivations
import qualified Language.Equivalence.Types as Types
import qualified Data.Map as Map
import Control.Monad.State


data Location = Location [Der] [Der]
  deriving (Show,Eq,Ord)

data CheckIndResult = CheckIndState (Map.Map Location Bool)
type CheckIndState a = StateT CheckIndResult IO a

checkInductive :: (Map.Map String Expr) -> Location -> IO Bool
checkInductive  invariants location = do
  let initialMap = Map.insert (Location [] []) True Map.empty
  evalStateT (checkInd invariants (Set.empty) location ) (CheckIndState  initialMap)

checkInd ::  (Map.Map String Expr) ->(Set.Set Location)-> Location -> CheckIndState Bool
checkInd invariants visited location = do
  (CheckIndState definedSet) <- get
  if Map.member location definedSet then return (Map.findWithDefault False location definedSet)
     else do
           result <- checkIndNewDers invariants location visited
           put (CheckIndState (Map.insert location result definedSet))
           return result


checkIndNewDers :: (Map.Map String Expr) -> Location ->(Set.Set Location)->CheckIndState Bool
checkIndNewDers invariants location visited = do
  entailResult <- liftIO (checkByEntail invariants location visited)
  if entailResult then return True
    else do
          splitResult <- checkBySplit invariants location visited
          if splitResult then return True
            else checkByUnwind invariants location visited
    

checkByEntail :: (Map.Map String Expr) -> Location ->(Set.Set Location)-> IO Bool
checkByEntail invariants location visitedSet = do
  let sameLocationList = Set.toList (Set.filter (isSameLocation location) visitedSet)
  resultList <- mapM (isEntailHolds invariants location) sameLocationList
  let list = takeWhile ( == False) resultList
  if length(list) == length(resultList) then return False
    else return True

-- this function need to re-implement, the order might not be right.
isEntailHolds :: (Map.Map String Expr) -> Location -> Location ->IO Bool
isEntailHolds invariants location1@(Location list1 list2) location2@(Location list3 list4) = do
  let predicateName1 = "R" ++ (foldr getPredicateName "" (list1++list2))
  let invariants1 = Map.findWithDefault (ExprConstant (ConstantBool False)) predicateName1 invariants
  let predicateName2 = "R" ++ (foldr getPredicateName "" (list3++list4))
  let invariants2 = Map.findWithDefault (ExprConstant (ConstantBool True)) predicateName2 invariants
  checkEntail invariants1 invariants2 

isSameLocation :: Location -> Location -> Bool
isSameLocation location1@(Location list1 list2) location2@(Location list3 list4) = do
  if (length(list1) /= length(list3)) ||  (length(list2) /= length(list4)) then False
    else do
         let isSameExprs1 = (zipWith isSameCoreExpr list1 list3)
         let isSameExprs2 = (zipWith isSameCoreExpr list2 list4)
         if  (elem False (isSameExprs1++isSameExprs2))  then False
            else True

getPredicateName :: Der -> String -> String
getPredicateName der@(Der _ _ _ _ idNumber) oldName =
  (show idNumber) ++ "!" ++ oldName

isSameCoreExpr :: Der -> Der -> Bool
isSameCoreExpr der1@(Der _ expr1 _ _ _) der2@(Der _ expr2 _ _ _) = do
  if expr1 == expr2 then True
    else False

checkBySplit :: (Map.Map String Expr) -> Location ->(Set.Set Location)->CheckIndState Bool
checkBySplit invariants location@(Location list1 list2) visited = do
  let splitLeft = splitLocation list1
  let splitRight = splitLocation list2
  let newLeftLocations = map (\(x,y) -> ((Location x list2),(Location y list2)) ) splitLeft
  let newRightLocations = map (\(x,y) -> ((Location list1 x),(Location list1 y)) ) splitRight
  let newVisited = Set.insert location visited
  resultLeft <- mapM (isPairInd invariants newVisited) newLeftLocations
  resultRight <- mapM (isPairInd invariants newVisited) newRightLocations
  if (elem True resultLeft) || (elem True resultRight) then return True
    else return False

isPairInd :: (Map.Map String Expr) -> (Set.Set Location) -> (Location,Location) -> CheckIndState Bool
isPairInd invariants visited (location1,location2) = do
  result1 <- checkInd invariants visited location1
  result2 <- checkInd invariants visited location2 
  return (result1 && result2)

-- need to change if we allowe arbitrary split
splitLocation :: [Der] -> [([Der],[Der])]
splitLocation location = map  ( (\x y -> splitAt y x) location) [1 .. ((length location)-1)]
 
checkByUnwind :: (Map.Map String Expr) -> Location ->(Set.Set Location)->CheckIndState Bool
checkByUnwind invariants location visited = do
 if (isRNSymbolic location) then return False
   else do
         let allUnwindLocation = unwind location
         let newVisited = Set.insert location visited
         result <- mapM (checkInd invariants newVisited) allUnwindLocation
         if (elem True result) then return True
           else return False

isRNSymbolic :: Location -> Bool
isRNSymbolic location@(Location [(Der RASym _ _ _ _)] []) = True
isRNSymbolic location@(Location [] [(Der RASym _ _ _ _)]) = True
isRNSymbolic _ = False

unwind :: Location -> [Location]
unwind location@(Location [x] []) = do
  let successor =collapseStepMark x
  [(Location successor [])]

unwind  location@(Location [] [x]) = do
  let successor = collapseStepMark x
  [(Location successor [])]

unwind location@(Location [x1] [x2]) = do
  let successor1  = collapseStepMark x1
  let successor2  = collapseStepMark x2
  [(Location successor1 [x2]),(Location [x1] successor2)]

unwind _ = []

collapseStepMark :: Der -> [Der]
collapseStepMark node@(Der _ _ _ successor _) = concat (map collapseStep successor)

collapseStep :: Der -> [Der]
collapseStep node@(Der RNFix _ _ _ _) = [node]
collapseStep node@(Der RASym _ _ _ _) = [node]
collapseStep node@(Der _ _ _ successor _ ) = concat (map collapseStep successor)


