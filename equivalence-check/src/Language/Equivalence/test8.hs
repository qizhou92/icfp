module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.Derivations
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.TypeInference
import Language.Equivalence.RelationalTypes
import Language.Equivalence.RelationalTypes


main = do
 let t1 = TProductId (TIntId 0) (TIntId 1) 2
 let t2 = TIntId 0
 let p1 = Pair t1 t2 [] []
 let productId = getTypeIndex isTypeProduct [t1,t2]
 print productId
 print (powerSet productId)

  
