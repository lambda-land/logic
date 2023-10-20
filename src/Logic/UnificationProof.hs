module Logic.UnificationProof (
  -- classes
  Unifiable (..),
  -- terms
  STerm (..),
  UTerm (..),
  -- rule interface
  Rule' (Rule),
  Rule,
  proofs
) where

import Data.Maybe (fromMaybe)
import Control.Monad (forM_, guard)
import Data.Foldable (traverse_)

import Data.Functor.Identity (Identity (..))
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State.Strict as State
import Control.Monad.Trans.State.Strict (StateT (StateT), evalStateT, execStateT)

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Logic.Proof (Proof (Node))
import Data.Fix (Fix (Fix))

-- borrowed from unification-fd's Control-Unification-Types
class Traversable t => Unifiable t where
    zipMatch :: t a -> t a -> Maybe (t (Either a (a, a)))

newtype MVar = MV Int deriving (Eq)

data UTerm t = UTerm (t (UTerm t))
             | UVar MVar

data STerm t = STerm (t (STerm t))
             | SVar String

data HeapCell t = HeapCell { name  :: String
                           , value :: UTerm t }

data Heap t = Heap { size :: Int
                   , refs :: IntMap (HeapCell t) }

emptyHeap :: Heap t
emptyHeap = Heap { size = 0, refs = IntMap.empty }

type Unification t = StateT (Heap t) []

deref' :: MVar -> Unification t (HeapCell t)
deref' (MV id) = State.gets (\(Heap _ refs) -> refs IntMap.! id)

deref :: MVar -> Unification t (Maybe (UTerm t))
deref (MV id) = StateT $ \h@(Heap _ refs) ->
    case refs IntMap.! id of
      HeapCell _ (UVar (MV id')) | id == id' -> [(Nothing, h)] -- unbound var
      HeapCell _ t                           -> [(Just t,  h)] -- link

assign :: MVar -> UTerm t -> Unification t ()
assign (MV id) t = StateT $ \(Heap size refs) ->
    let HeapCell name value = refs IntMap.! id in
    case value of
      UVar (MV id') | id == id' -> let cell' = HeapCell name t in
                                   let refs' = IntMap.insert id cell' refs in
                                   [((), Heap size refs')]
      _                         -> error $ "cannot reassign var: " ++ name

newVar :: String -> Unification t MVar
newVar name =
  StateT $ \(Heap size refs) ->
    let mv = MV size in
    [(mv, Heap {
      size = size + 1,
      refs = IntMap.insert size
                           HeapCell { name  = name
                                    , value = UVar mv }
                           refs
    })]

-- across a collection of terms:
-- replace string variables with metavariables
s2u :: (Traversable t, Traversable f) => f (STerm t) -> Unification t (f (UTerm t))
s2u = \t -> evalStateT (traverse walk t) Map.empty where
    walk :: Traversable t => STerm t -> StateT (Map String (UTerm t)) (Unification t) (UTerm t)
    walk (STerm t) = UTerm <$> traverse walk t
    walk (SVar s)  = do maybe <- State.gets (Map.lookup s)
                        case maybe of
                          Just t  -> pure t
                          Nothing -> do t <- lift (UVar <$> newVar s)
                                        State.modify (Map.insert s t)
                                        pure t

-- across a collection of terms:
-- replace unsolved metavariables with string variables
u2s :: (Traversable t, Traversable f) => f (UTerm t) -> Unification t (f (STerm t))
u2s = \t -> do dvs <- duplicateVars t
               let needsNumbering s = case dvs Map.! s of Nothing -> True
                                                          Just _  -> False
               evalStateT (traverse (walk needsNumbering) t) (Map.empty, IntMap.empty)
  where
    walk :: Traversable t    =>
            (String -> Bool) ->
            UTerm t          -> StateT (Map String Int, IntMap (STerm t)) (Unification t) (STerm t)
    walk nn (UTerm t) = STerm <$> traverse (walk nn) t
    walk nn (UVar v)  = do
      dereferenced <- lift $ deref' v
      case dereferenced of
        HeapCell name (UVar v') | v == v' -> replaceVar name v
        HeapCell _    t                   -> walk nn t
      where
        replaceVar name (MV id)
          | not (nn name) = pure (SVar name)
          | otherwise     = do
               (counts, names) <- State.get
               case names IntMap.!? id of
                 Just t  -> pure t
                 Nothing -> do
                   let count = 1 + fromMaybe 0 (counts Map.!? name)
                   let svar = SVar (name ++ show count)
                   let counts' = Map.insert name count counts
                   let names'  = IntMap.insert id svar names
                   State.put (counts', names')
                   pure svar

    duplicateVars :: (Traversable t, Traversable f) => f (UTerm t) -> Unification t (Map String (Maybe MVar))
    duplicateVars = \t -> execStateT (traverse_ walk t) Map.empty where
      walk (UTerm t) = traverse_ walk t
      walk (UVar v)  = do
        dereferenced <- lift $ deref' v
        case dereferenced of
          HeapCell name (UVar v') | v == v' -> handleVar name v
          HeapCell _    t                   -> walk t
        where
          handleVar name v = State.modify (Map.insertWith merge name (Just v))
          merge (Just v1) (Just v2) | v1 == v2 = Just v1
          merge _         _                    = Nothing

unify :: Unifiable t => UTerm t -> UTerm t -> Unification t ()
unify t1 t2 = unifyLoc (Nothing, t1) (Nothing, t2)

unifyLoc :: Unifiable t =>
            (Maybe MVar, UTerm t) ->
            (Maybe MVar, UTerm t) ->
            Unification t ()
unifyLoc (Just l1, _) (Just l2, _) | l1 == l2 = pure ()
unifyLoc (_, UTerm t1) (_, UTerm t2) =
    case zipMatch t1 t2 of
      Nothing       -> lift []
      Just subterms -> forM_ subterms $ \subt -> case subt of Left  _      -> pure ()
                                                              Right (a, b) -> unify a b
unifyLoc t (_, UVar v) = unifyVarTerm v t
unifyLoc (_, UVar v) t = unifyVarTerm v t

unifyVarTerm :: Unifiable t => MVar -> (Maybe MVar, UTerm t) -> Unification t ()
unifyVarTerm v t = do
    dereferenced <- deref v
    case dereferenced of
      Just t' -> unifyLoc (Just v, t') t
      Nothing -> do
        occurs v (snd t) >>= guard . not
        assign v (snd t)

occurs :: Traversable t => MVar -> UTerm t -> Unification t Bool
occurs v (UVar v') | v == v'   = pure True
                   | otherwise = do dereferenced <- deref v'
                                    case dereferenced of
                                      Just t' -> occurs v t'
                                      Nothing -> pure False
occurs v (UTerm t) = or <$> traverse (occurs v) t

data Rule' a = Rule a [a] deriving (Functor, Foldable, Traversable)
type Rule t = Rule' (STerm t)

proofs :: forall t. Unifiable t => [Rule t] -> STerm t -> [Proof (STerm t)]
proofs rules = \conclusion -> flip evalStateT emptyHeap $ do Identity conclusion' <- s2u (Identity conclusion)
                                                             tree <- search conclusion'
                                                             u2s tree
  where
    -- search :: UTerm t -> Unification t (Proof (UTerm t))
    search conclusion = do
      rule <- lift rules
      Rule conclusion' premises' <- s2u rule
      unify conclusion conclusion'
      Node conclusion <$> traverse search premises'
