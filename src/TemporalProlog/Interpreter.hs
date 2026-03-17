module TemporalProlog.Interpreter
  ( InterpreterState(..)
  , newInterpreterState
  , stepWorld
  , stepWorldN
  , assertFact
  , queryAtom
  , currentWorld
  , getHistory
  , getWorldNumber
  ) where

import Control.Monad (guard)
import Data.List (nub, partition)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)

import TemporalProlog.Syntax
import TemporalProlog.Unification

-- | The interpreter state tracks the current world, history, and program
data InterpreterState = InterpreterState
  { isProgram    :: NormalProgram
  , isWorlds     :: [World]      -- worlds in reverse order: head is most recent
  , isWorldNum   :: Int          -- current world number
  , isAssertions :: [GroundAtom] -- facts asserted for the next step
  } deriving (Show)

newInterpreterState :: NormalProgram -> InterpreterState
newInterpreterState prog = InterpreterState
  { isProgram    = prog
  , isWorlds     = []
  , isWorldNum   = -1  -- will become 0 on first step
  , isAssertions = []
  }

currentWorld :: InterpreterState -> Maybe World
currentWorld st = case isWorlds st of
  (w:_) -> Just w
  []    -> Nothing

getHistory :: InterpreterState -> [World]
getHistory = reverse . isWorlds

getWorldNumber :: InterpreterState -> Int
getWorldNumber = isWorldNum

-- | Assert a ground atom for the next world computation
assertFact :: GroundAtom -> InterpreterState -> InterpreterState
assertFact a st = st { isAssertions = a : isAssertions st }

-- | Query whether an atom matches anything in the current world
queryAtom :: Atom -> InterpreterState -> [Subst]
queryAtom pat st = case currentWorld st of
  Nothing -> []
  Just w  -> mapMaybe (matchAtom pat) (Set.toList w)

-- | Advance the interpreter by one world
stepWorld :: InterpreterState -> InterpreterState
stepWorld st =
  let worldNum = isWorldNum st + 1
      history = isWorlds st  -- reverse order, head = most recent (world n-1)
      assertions = Set.fromList (isAssertions st)
      prog = isProgram st
      -- Compute the new world via least fixed point
      newWorld = computeWorld prog history assertions worldNum
  in st { isWorlds     = newWorld : history
        , isWorldNum   = worldNum
        , isAssertions = []
        }

-- | Step N worlds
stepWorldN :: Int -> InterpreterState -> InterpreterState
stepWorldN 0 st = st
stepWorldN n st = stepWorldN (n-1) (stepWorld st)

-- | Compute a world by finding the least fixed point of all rules
computeWorld :: NormalProgram -> [World] -> Set GroundAtom -> Int -> World
computeWorld prog history assertions worldNum =
  let -- Stratify the program
      strata = stratify prog
      -- Process each stratum in order, accumulating the world
      initialWorld = assertions `Set.union` externalFacts worldNum
  in foldl (processStratum history worldNum) initialWorld strata

-- | External/built-in facts for a given world number
externalFacts :: Int -> Set GroundAtom
externalFacts n = Set.fromList
  [ Atom "at" [TFun (show n) []]
  , Atom "true" []
  ]

-- | Maximum iterations for fixed-point computation per stratum.
--   Prevents divergence on programs that generate infinite ground atoms.
maxFixedPointIterations :: Int
maxFixedPointIterations = 10000

-- | Process one stratum: compute fixed point for its rules
processStratum :: [World] -> Int -> World -> [NormalRule] -> World
processStratum history worldNum world rules = go maxFixedPointIterations world
  where
    go 0 w = w  -- fuel exhausted; return current approximation
    go fuel w =
      let w' = applyRulesOnce rules history worldNum w
      in if w' == w then w else go (fuel - 1) w'

-- | Apply all rules once, returning the union of derived facts with the current world
applyRulesOnce :: [NormalRule] -> [World] -> Int -> World -> World
applyRulesOnce rules history worldNum world =
  let derived = concatMap (\r -> deriveFromRule r history worldNum world) rules
  in world `Set.union` Set.fromList derived

-- | Derive all possible ground atoms from a single rule
deriveFromRule :: NormalRule -> [World] -> Int -> World -> [GroundAtom]
deriveFromRule (NormalRule conds headAtom) history worldNum world =
  let -- Find all substitutions that satisfy all conditions
      substs = findSatisfyingSubsts conds history worldNum world
      -- Apply each substitution to the head
      heads = map (\s -> applySubstAtom s headAtom) substs
      -- Only keep ground results
  in filter isGroundAtom heads

-- | Find all substitutions satisfying a list of conditions.
--   Reorders so positive conditions are processed before negative ones
--   (standard safety condition for negation-as-failure).
findSatisfyingSubsts :: [NormalCond] -> [World] -> Int -> World -> [Subst]
findSatisfyingSubsts conds history worldNum world =
  let (pos, neg) = partition (\c -> not (ncNegated c)) conds
      ordered = pos ++ neg
  in go ordered history worldNum world
  where
    go [] _ _ _ = [emptySubst]
    go (c:cs) hist wn w = do
      s1 <- satisfyCond c hist wn w
      let cs' = map (applySubstNormalCond s1) cs
      s2 <- go cs' hist wn w
      return (composeSubst s2 s1)

-- | Find all substitutions that satisfy a single normal condition
satisfyCond :: NormalCond -> [World] -> Int -> World -> [Subst]
satisfyCond (NormalCond depth negated atom) history worldNum world =
  let targetWorld = lookupWorld depth history worldNum world
  in case targetWorld of
    Nothing ->
      -- Past world doesn't exist (before time 0)
      if negated
        then [emptySubst]  -- negation of something in non-existent world is true
        else []
    Just tw ->
      if negated
        then satisfyNegated atom tw world worldNum
        else satisfyPositive atom tw worldNum

-- | Look up a world at depth d in the past
--   depth 0 = current world being constructed
--   depth 1 = previous world (head of history)
--   depth 2 = two worlds ago, etc.
lookupWorld :: Int -> [World] -> Int -> World -> Maybe World
lookupWorld 0 _ _ currentW = Just currentW
lookupWorld d history _worldNum _ =
  let idx = d - 1  -- history is [most recent, ..., oldest]
  in if idx < length history
     then Just (history !! idx)
     else Nothing  -- before time began

-- | Find substitutions for a positive atom against a world
satisfyPositive :: Atom -> World -> Int -> [Subst]
satisfyPositive pat world worldNum =
  -- Check external predicates first
  case evaluateExternal pat worldNum of
    Just substs -> substs
    Nothing     -> mapMaybe (matchAtom pat) (Set.toList world)

-- | Find substitutions for a negated atom (negation-as-failure)
satisfyNegated :: Atom -> World -> World -> Int -> [Subst]
satisfyNegated atom targetWorld _currentWorld worldNum =
  -- For negation-as-failure: ~p(X) is true if there is no instance of p in the world
  -- If atom is ground, check if it's NOT in the world
  if isGroundAtom atom
    then if atom `Set.notMember` targetWorld && null (fromMaybe [] (evaluateExternal atom worldNum))
         then [emptySubst]
         else []
    else
      -- For non-ground negated atoms, we need to check if there are NO matching
      -- instances. This is tricky with free variables in negated conditions.
      -- For safety, we require negated atoms to be ground after substitution
      -- from positive conditions. If still non-ground, treat as failure.
      if null (satisfyPositive atom targetWorld worldNum)
        then [emptySubst]
        else []

-- | Evaluate external/built-in predicates
evaluateExternal :: Atom -> Int -> Maybe [Subst]
evaluateExternal (Atom "true" []) _ = Just [emptySubst]
evaluateExternal (Atom "false" []) _ = Just []
evaluateExternal (Atom "=" [t1, t2]) _ =
  case unifyTerm t1 t2 of
    Just s  -> Just [s]
    Nothing -> Just []
evaluateExternal (Atom ">" [t1, t2]) _ = boolExternal $ compareTerm t1 t2 (>)
evaluateExternal (Atom "<" [t1, t2]) _ = boolExternal $ compareTerm t1 t2 (<)
evaluateExternal (Atom ">=" [t1, t2]) _ = boolExternal $ compareTerm t1 t2 (>=)
evaluateExternal (Atom "<=" [t1, t2]) _ = boolExternal $ compareTerm t1 t2 (<=)
evaluateExternal (Atom "at" [t]) worldNum = Just $ case t of
  TVar v -> [Map.singleton v (TFun (show worldNum) [])]
  TFun s [] | s == show worldNum -> [emptySubst]
  _ -> []
evaluateExternal _ _ = Nothing

boolExternal :: Maybe Bool -> Maybe [Subst]
boolExternal (Just True) = Just [emptySubst]
boolExternal (Just False) = Just []
boolExternal Nothing = Nothing

-- | Try to compare terms as numbers
compareTerm :: Term -> Term -> (Int -> Int -> Bool) -> Maybe Bool
compareTerm t1 t2 op = do
  n1 <- termToInt t1
  n2 <- termToInt t2
  return (op n1 n2)

termToInt :: Term -> Maybe Int
termToInt (TFun s []) = case reads s of
  [(n, "")] -> Just n
  _         -> Nothing
termToInt _ = Nothing

-- ============================================================
-- Stratification
-- ============================================================

-- | Compute dependency strata for the program.
--   Simple approach: predicates that depend negatively on each other
--   go in different strata. Positive dependencies can be in the same stratum.
stratify :: NormalProgram -> [[NormalRule]]
stratify prog =
  let strataMap = computeStrata prog
      maxStratum = if Map.null strataMap then 0
                   else maximum (Map.elems strataMap)
  in [filter (\r -> Map.findWithDefault 0 (predName (nrHead r)) strataMap == s) prog
     | s <- [0..maxStratum]]

predName :: Atom -> Name
predName (Atom n _) = n

data DepKind = Positive | Negative deriving (Eq, Ord, Show)

buildDeps :: NormalProgram -> Map Name [(Name, DepKind)]
buildDeps prog = Map.fromListWith (++) $ do
  rule <- prog
  let hd = predName (nrHead rule)
  cond <- nrConditions rule
  -- Per the paper: eliminate conditions with @ (they reference past worlds,
  -- not the current fixed-point computation, so they don't create dependencies)
  guard (ncPrevDepth cond == 0)
  let dep = predName (ncAtom cond)
      kind = if ncNegated cond then Negative else Positive
  return (hd, [(dep, kind)])

computeStrata :: NormalProgram -> Map Name Int
computeStrata prog =
  let deps = buildDeps prog
      allPreds = nub $ map (predName . nrHead) prog
      initial = Map.fromList [(p, 0) | p <- allPreds]
      result = fixStrata deps initial (length allPreds + 1)
  in result

fixStrata :: Map Name [(Name, DepKind)] -> Map Name Int -> Int -> Map Name Int
fixStrata _ m 0 = Map.map (const 0) m  -- Diverged: fall back to single stratum
fixStrata deps m fuel =
  let m' = Map.mapWithKey (updateStratum deps m) m
  in if m' == m then m else fixStrata deps m' (fuel - 1)

updateStratum :: Map Name [(Name, DepKind)] -> Map Name Int -> Name -> Int -> Int
updateStratum deps current name_ currentStratum =
  case Map.lookup name_ deps of
    Nothing -> currentStratum
    Just depList ->
      let negNeeded = [Map.findWithDefault 0 dep current + 1
                      | (dep, Negative) <- depList]
          posNeeded = [Map.findWithDefault 0 dep current
                      | (dep, Positive) <- depList]
      in maximum (currentStratum : negNeeded ++ posNeeded)
