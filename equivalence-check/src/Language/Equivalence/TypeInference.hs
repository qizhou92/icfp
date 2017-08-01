module Language.Equivalence.TypeInference where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Equivalence.Types

type TV = String
data Type = TVar TV
           | TInt
           | TBool
           | TArr Type Type
  deriving (Eq, Ord)

data Scheme = Forall [Type] Type

newtype TypeEnv = TypeEnv (Map.Map Type Scheme)

type Subst = Map.Map Type Type

class Substitutable a where
  apply  :: Subst -> a -> a
  freeTvars :: a -> Set.Set Type

instance Substitutable Type where
  apply _ TInt = TInt
  apply _ TBool = TBool
  apply subSet t@(TVar a) = Map.findWithDefault t t subSet
  apply subSet t@(TArr t1 t2) = (TArr (apply subSet t1) (apply subSet t2))

  freeTvars TInt = Set.empty
  freeTvars TBool = Set.empty
  freeTvars (TVar a) = Set.singleton (TVar a)
  freeTvars (TArr t1 t2) = (Set.union (freeTvars t1) (freeTvars t2) )

instance Substitutable Scheme where
  apply subSet (Forall boundVars t) = Forall boundVars (apply newSubSet t) 
                                      where newSubSet = foldr Map.delete subSet boundVars
  freeTvars (Forall boundVars t) = Set.difference (freeTvars t) (Set.fromList boundVars)

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  freeTvars = foldr Set.union Set.empty . map freeTvars

instance  Substitutable TypeEnv where
  apply s (TypeEnv typeEnv) = TypeEnv  (Map.map (apply s) typeEnv)
  freeTvars (TypeEnv typeEnv) = freeTvars (Map.elems typeEnv)

andSubSet :: Subst -> Subst -> Subst
andSubSet s1 s2 = (Map.union) (Map.map (apply s1) s2) s1 

