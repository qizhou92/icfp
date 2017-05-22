module Language.Haskell.VerifyDerivation where

import Language.Haskell.CHC
import Language.Haskell.Expr

-- Subexprssion is the data type represents the subexprrsion in derivation, first argument 
-- string represents the name of the subexprssion, second argument list of string represents the list of variable name 
-- Int represents the count of SubExprssion

data SubExprssion = SubExprssion String [Var] Int


data HyperEdge = HyperEdge Expr [DerivationNode]

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode SubExprssion HyperEdge

-- repalce the int data type by subexpression to get all merge/split subexpression possible set


getAllPossibleList:: [Int] -> [ [ [Int] ]]
getAllPossibleList list = case list of
  x:xs -> (insertElementIntoAllList x (getAllPossibleList xs))
  otherwise -> []

insertElementIntoAllList :: Int -> [ [ [ Int ]]] -> [ [ [Int] ] ]

insertElementIntoAllList element list = case list of
  [] -> [[[element]]] 
  otherwise->(insertElementIntoAllList1 element list) ++ (insertElementIntoAllList2 element list)

insertElementIntoAllList1 :: Int -> [ [ [ Int ]]] -> [ [ [Int] ] ] 
insertElementIntoAllList1 element list = case list of
  x:xs -> if null x 
          then [[element]]:(insertElementIntoAllList1 element xs)
          else ([element]:x):(insertElementIntoAllList1 element xs)
  otherwise -> []

insertElementIntoAllList2 :: Int -> [ [ [Int] ]]  -> [ [ [Int] ] ] 
insertElementIntoAllList2 element list = case list of
	x:xs -> (insertAllIndex element (length(x)) x) ++ (insertElementIntoAllList2 element xs)
	otherwise -> []

insertAllIndex :: Int -> Int -> [ [Int] ] -> [ [ [Int] ] ]
insertAllIndex element len oldList 
  | 0<len = (insertByIndex (len - 1) element oldList) : (insertAllIndex element (len -1) oldList)
  | otherwise = []

insertByIndex :: Int -> Int -> [ [Int] ] -> [ [ Int ] ]
insertByIndex index element (x:xs)  
  |0<index = x:(insertByIndex (index -1) element xs)
  |otherwise =  (element:x):xs
