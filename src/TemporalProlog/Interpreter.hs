-- |
-- Module      : TemporalProlog.Interpreter
-- Description : Hybrid forward/backward-chaining execution engine (paper §5.2)
--
-- Executes a normalized Temporal Prolog program by computing a sequence
-- of worlds (sets of ground atoms). Each world is the least fixed point
-- of the program's forward-chaining rules applied to:
--
-- * Externally asserted facts for that time step
-- * Built-in facts ('at', 'true')
-- * Atoms derivable from rules referencing the current and past worlds
--
-- __Pattern functions__ (e.g. @append@) are resolved via backward
-- chaining (SLD-resolution) rather than stored in the world set. Their
-- defining rules are excluded from stratification and the forward-chaining
-- fixed point. This allows recursive definitions to work naturally.
--
-- __Stratified negation.__ Negation-as-failure requires that rules be
-- stratified: predicates involved in negative dependency cycles are
-- rejected. The dependency graph intentionally excludes conditions with
-- @\@-depth > 0@ since those reference already-computed past worlds and
-- do not participate in the current fixed-point (paper §5.2).
--
-- __Closed World Assumption.__ Any ground atom not derivable in a world
-- is considered false. Negated conditions succeed when no matching
-- positive instance exists.
--
-- __External predicates.__ @=@, @>@, @<@, @>=@, @<=@, @+@, @-@, @*@,
-- @true@, @false@, and @at(N)@ are evaluated specially, not stored in
-- the world set.
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
  , traceDerivations
  ) where

import Control.Monad (guard)
import Data.List (partition)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
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
  , isWorlds     :: IntMap World  -- world number -> world (O(log n) lookup)
  , isWorldNum   :: Maybe Int     -- current world number (Nothing before first step)
  , isAssertions :: [GroundAtom]  -- facts asserted for the next step
  , isPFNames    :: Set Name      -- pattern-function predicate names (backward-chaining)
  , isTraces     :: Map GroundAtom [NormalRule]  -- derivation provenance for current world
  } deriving (Show)

newInterpreterState :: NormalProgram -> Set Name -> InterpreterState
newInterpreterState prog pfNames = InterpreterState
  { isProgram    = prog
  , isWorlds     = IntMap.empty
  , isWorldNum   = Nothing
  , isAssertions = []
  , isPFNames    = pfNames
  , isTraces     = Map.empty
  }

currentWorld :: InterpreterState -> Maybe World
currentWorld st = case isWorldNum st of
  Nothing -> Nothing
  Just n  -> IntMap.lookup n (isWorlds st)

getHistory :: InterpreterState -> [World]
getHistory st = map snd (IntMap.toAscList (isWorlds st))

getWorldNumber :: InterpreterState -> Maybe Int
getWorldNumber = isWorldNum

-- | Assert a ground atom for the next world computation
assertFact :: GroundAtom -> InterpreterState -> InterpreterState
assertFact a st = st { isAssertions = a : isAssertions st }

-- | Query whether an atom matches anything in the current world.
--   For pattern-function predicates, dispatches to the backward chainer
--   since PF atoms are never stored in the world set.
queryAtom :: Atom -> InterpreterState -> [Subst]
queryAtom pat st =
  let pfNames = isPFNames st
      prog = isProgram st
      (pfRules, _) = partition (\r -> predName (nrHead r) `Set.member` pfNames) prog
      worldNum = case isWorldNum st of
        Nothing -> 0
        Just n  -> n
      worlds = isWorlds st
  in if predName pat `Set.member` pfNames
     then solveBackward pfNames pfRules pat
            (maybe emptyWorld id (currentWorld st)) worlds worldNum 0
     else case currentWorld st of
            Nothing -> []
            Just w  -> matchInWorld pat w

-- | Advance the interpreter by one world
stepWorld :: InterpreterState -> Either String InterpreterState
stepWorld st =
  let worldNum = case isWorldNum st of
        Nothing -> 0
        Just n  -> n + 1
      worlds = isWorlds st
      assertions = worldFromList (isAssertions st)
      prog = isProgram st
      pfNames = isPFNames st
  in case computeWorld prog pfNames worlds assertions worldNum of
    Left err -> Left err
    Right (newWorld, traces) ->
      Right st { isWorlds     = IntMap.insert worldNum newWorld worlds
               , isWorldNum   = Just worldNum
               , isAssertions = []
               , isTraces     = traces
               }

-- | Step N worlds
stepWorldN :: Int -> InterpreterState -> Either String InterpreterState
stepWorldN 0 st = Right st
stepWorldN n st = case stepWorld st of
  Left err -> Left err
  Right st' -> stepWorldN (n-1) st'

-- | Compute a world by stratified fixed-point iteration.
--   Returns the computed world and derivation traces.
computeWorld :: NormalProgram -> Set Name -> IntMap World -> World -> Int
             -> Either String (World, Map GroundAtom [NormalRule])
computeWorld prog pfNames worlds assertions worldNum =
  let -- Partition rules: PF-defining rules go to backward chainer,
      -- forward-chaining rules go through stratification
      (pfRules, fcRules) = partition (\r -> predName (nrHead r) `Set.member` pfNames) prog
      -- Process each stratum in order, accumulating the world
      initialWorld = assertions `worldUnion` externalFacts worldNum
  in case stratify fcRules of
    Left err -> Left err
    Right strata ->
      foldl (\acc stratumRules -> do
              (w, ts) <- acc
              (w', ts') <- processStratum pfNames pfRules worlds worldNum w stratumRules
              Right (w', Map.unionWith (++) ts ts'))
            (Right (initialWorld, Map.empty))
            strata

-- | External/built-in facts for a given world number
externalFacts :: Int -> World
externalFacts n = worldFromList
  [ Atom "at" [TFun (show n) []]
  , Atom "true" []
  ]

-- | Maximum iterations for fixed-point computation per stratum.
--   Prevents divergence on programs that generate infinite ground atoms.
maxFixedPointIterations :: Int
maxFixedPointIterations = 10000

-- | Process one stratum: compute fixed point for its rules.
--   Returns the final world and derivation traces, or an error if the
--   fixed point does not converge within the iteration limit.
processStratum :: Set Name -> [NormalRule] -> IntMap World -> Int -> World -> [NormalRule]
               -> Either String (World, Map GroundAtom [NormalRule])
processStratum pfNames pfRules worlds worldNum world rules = go maxFixedPointIterations world Map.empty
  where
    go 0 _ _ = Left $ "Fixed-point computation did not converge within "
                    ++ show maxFixedPointIterations ++ " iterations at world "
                    ++ show worldNum ++ ". The program may generate unbounded ground atoms."
    go fuel w ts =
      let (w', newTraces) = applyRulesOnce pfNames pfRules rules worlds worldNum w
      in if w' == w then Right (w, ts) else go (fuel - 1) w' (Map.unionWith (++) ts newTraces)

-- | Apply all rules once, returning the union of derived facts with the current world
--   and traces for newly derived facts.
applyRulesOnce :: Set Name -> [NormalRule] -> [NormalRule] -> IntMap World -> Int -> World
               -> (World, Map GroundAtom [NormalRule])
applyRulesOnce pfNames pfRules rules worlds worldNum world =
  let derivations = concatMap (\r -> map (\a -> (a, r)) (deriveFromRule pfNames pfRules r worlds worldNum world)) rules
      newWorld = foldl (\w (a, _) -> worldInsert a w) world derivations
      -- Only trace newly derived facts (not already in world)
      newTraces = Map.fromListWith (++)
        [(a, [r]) | (a, r) <- derivations, not (worldMember a world)]
  in (newWorld, newTraces)

-- | Derive all possible ground atoms from a single rule
deriveFromRule :: Set Name -> [NormalRule] -> NormalRule -> IntMap World -> Int -> World -> [GroundAtom]
deriveFromRule pfNames pfRules (NormalRule conds headAtom) worlds worldNum world =
  let -- Find all substitutions that satisfy all conditions
      substs = findSatisfyingSubsts pfNames pfRules conds worlds worldNum world
      -- Apply each substitution to the head
      heads = map (\s -> applySubstAtom s headAtom) substs
      -- Only keep ground results
  in filter isGroundAtom heads

-- | Find all substitutions satisfying a list of conditions.
--   Reorders so positive conditions are processed before negative ones
--   (standard safety condition for negation-as-failure).
findSatisfyingSubsts :: Set Name -> [NormalRule] -> [NormalCond] -> IntMap World -> Int -> World -> [Subst]
findSatisfyingSubsts pfNames pfRules conds worlds worldNum world =
  let (pos, neg) = partition (\c -> not (ncNegated c)) conds
      ordered = pos ++ neg
  in go ordered worlds worldNum world
  where
    go [] _ _ _ = [emptySubst]
    go (c:cs) ws wn w = do
      s1 <- satisfyCond pfNames pfRules c ws wn w
      let cs' = map (applySubstNormalCond s1) cs
      s2 <- go cs' ws wn w
      return (composeSubst s2 s1)

-- | Find all substitutions that satisfy a single normal condition
satisfyCond :: Set Name -> [NormalRule] -> NormalCond -> IntMap World -> Int -> World -> [Subst]
satisfyCond pfNames pfRules (NormalCond depth negated atom) worlds worldNum world =
  let targetWorld = lookupWorld depth worlds worldNum world
  in case targetWorld of
    Nothing ->
      -- Past world doesn't exist (before time 0)
      if negated
        then [emptySubst]  -- negation of something in non-existent world is true
        else []
    Just tw ->
      let effectiveWorldNum = worldNum - depth
      in if negated
        then satisfyNegated pfNames pfRules atom tw worlds world effectiveWorldNum
        else satisfyPositive pfNames pfRules atom tw worlds effectiveWorldNum

-- | Look up a world at depth d in the past.
--   depth 0 = current world being constructed
--   depth 1 = previous world, etc.
--   O(log n) via IntMap lookup.
lookupWorld :: Int -> IntMap World -> Int -> World -> Maybe World
lookupWorld 0 _ _ currentW = Just currentW
lookupWorld d worlds worldNum _ =
  let pastWorldNum = worldNum - d
  in if pastWorldNum >= 0
     then IntMap.lookup pastWorldNum worlds
     else Nothing  -- before time began

-- | Find substitutions for a positive atom against a world.
--   Uses the predicate-name index for O(log p + k) lookup where
--   p = number of predicates and k = atoms with matching predicate.
satisfyPositive :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int -> [Subst]
satisfyPositive pfNames pfRules pat world worlds worldNum =
  -- Check external predicates first
  case evaluateExternal pat worldNum of
    Just substs -> substs
    Nothing
      -- If this is a pattern-function predicate, use backward chaining
      | predName pat `Set.member` pfNames ->
          solveBackward pfNames pfRules pat world worlds worldNum 0
      | otherwise -> matchInWorld pat world

-- | Match a pattern atom against all atoms in a world with matching predicate.
matchInWorld :: Atom -> World -> [Subst]
matchInWorld pat w =
  let candidates = worldLookupPred (predName pat) w
  in mapMaybe (matchAtom pat) (Set.toList candidates)

-- | Find substitutions for a negated atom (negation-as-failure)
satisfyNegated :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> World -> Int -> [Subst]
satisfyNegated pfNames pfRules atom targetWorld worlds _currentWorld worldNum =
  -- For negation-as-failure: ~p(X) is true if there is no instance of p in the world.
  -- For PF predicates we must always consult the backward chainer, since PF atoms
  -- are never stored in the world set.
  if isGroundAtom atom && not (predName atom `Set.member` pfNames)
    then if not (worldMember atom targetWorld) && null (fromMaybe [] (evaluateExternal atom worldNum))
         then [emptySubst]
         else []
    else
      -- For non-ground atoms or PF predicates, check via satisfyPositive
      -- (which dispatches to backward chaining for PF predicates).
      if null (satisfyPositive pfNames pfRules atom targetWorld worlds worldNum)
        then [emptySubst]
        else []

-- ============================================================
-- External predicates and arithmetic evaluation
-- ============================================================

-- | Evaluate built-in predicates that don't participate in the world set.
--   Returns substitutions rather than booleans so that @=@ can unify
--   and @at(X)@ can bind variables.
evaluateExternal :: Atom -> Int -> Maybe [Subst]
evaluateExternal (Atom "true" []) _ = Just [emptySubst]
evaluateExternal (Atom "false" []) _ = Just []
evaluateExternal (Atom "=" [t1, t2]) _ =
  case unifyTerm t1 t2 of
    Just s  -> Just [s]
    Nothing -> Just []
evaluateExternal (Atom "is" [result, expr]) _ =
  case evalArith expr of
    Just n  ->
      let nTerm = TFun (show n) []
      in case unifyTerm result nTerm of
           Just s  -> Just [s]
           Nothing -> Just []
    Nothing -> Nothing
evaluateExternal (Atom ">" [t1, t2]) _ = boolExternal $ compareArith t1 t2 (>)
evaluateExternal (Atom "<" [t1, t2]) _ = boolExternal $ compareArith t1 t2 (<)
evaluateExternal (Atom ">=" [t1, t2]) _ = boolExternal $ compareArith t1 t2 (>=)
evaluateExternal (Atom "<=" [t1, t2]) _ = boolExternal $ compareArith t1 t2 (<=)
evaluateExternal (Atom "at" [t]) worldNum = Just $ case t of
  TVar v -> [Map.singleton v (TFun (show worldNum) [])]
  TFun s [] | s == show worldNum -> [emptySubst]
  _ -> []
evaluateExternal _ _ = Nothing

boolExternal :: Maybe Bool -> Maybe [Subst]
boolExternal (Just True) = Just [emptySubst]
boolExternal (Just False) = Just []
boolExternal Nothing = Nothing

-- | Evaluate an arithmetic expression to an integer.
--   Supports +, -, *, div, mod, and integer literals.
evalArith :: Term -> Maybe Int
evalArith (TFun s []) = case reads s of
  [(n, "")] -> Just n
  _         -> Nothing
evalArith (TFun "+" [a, b]) = (+) <$> evalArith a <*> evalArith b
evalArith (TFun "-" [a, b]) = (-) <$> evalArith a <*> evalArith b
evalArith (TFun "*" [a, b]) = (*) <$> evalArith a <*> evalArith b
evalArith (TFun "div" [a, b]) = do
  x <- evalArith a
  y <- evalArith b
  if y == 0 then Nothing else Just (x `div` y)
evalArith (TFun "mod" [a, b]) = do
  x <- evalArith a
  y <- evalArith b
  if y == 0 then Nothing else Just (x `mod` y)
evalArith _ = Nothing

-- | Compare two terms arithmetically.
--   Both sides are evaluated as arithmetic expressions before comparison.
compareArith :: Term -> Term -> (Int -> Int -> Bool) -> Maybe Bool
compareArith t1 t2 op = do
  n1 <- evalArith t1
  n2 <- evalArith t2
  return (op n1 n2)

-- ============================================================
-- Backward chaining for pattern-function predicates
-- ============================================================

-- | Maximum recursion depth for backward chaining
maxBCDepth :: Int
maxBCDepth = 100

-- | Solve a goal atom by backward chaining over PF-defining rules.
--   Returns all substitutions that make the goal true.
solveBackward :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int -> Int -> [Subst]
solveBackward _pfNames _pfRules _goal _world _worlds _worldNum depth
  | depth >= maxBCDepth = []  -- depth limit reached
solveBackward pfNames pfRules goal world worlds worldNum depth =
  concatMap (\(i, rule) -> tryBCRule pfNames pfRules goal world worlds worldNum depth i rule)
            (zip [0..] pfRules)

-- | Try to use a single PF rule to satisfy a goal.
--   Alpha-renames the rule, unifies its head with the goal, then solves conditions.
tryBCRule :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int -> Int -> Int -> NormalRule -> [Subst]
tryBCRule pfNames pfRules goal world worlds worldNum depth idx rule =
  let renamedRule = renameRuleVars depth idx rule
      rHead = nrHead renamedRule
      rConds = nrConditions renamedRule
  in case unifyAtom goal rHead of
    Nothing -> []
    Just s ->
      let conds' = map (applySubstNormalCond s) rConds
      in map (\s2 -> composeSubst s2 s) (solveBCConds pfNames pfRules conds' world worlds worldNum depth)

-- | Solve a list of conditions sequentially, threading substitutions.
solveBCConds :: Set Name -> [NormalRule] -> [NormalCond] -> World -> IntMap World -> Int -> Int -> [Subst]
solveBCConds _pfNames _pfRules [] _world _worlds _worldNum _depth = [emptySubst]
solveBCConds pfNames pfRules (c:cs) world worlds worldNum depth = do
  s1 <- solveBCCond pfNames pfRules c world worlds worldNum depth
  let cs' = map (applySubstNormalCond s1) cs
  s2 <- solveBCConds pfNames pfRules cs' world worlds worldNum depth
  return (composeSubst s2 s1)

-- | Solve a single condition in backward-chaining context.
--   PF predicates recurse; others fall back to world lookup.
--   Respects @-depth by looking up the appropriate past world.
solveBCCond :: Set Name -> [NormalRule] -> NormalCond -> World -> IntMap World -> Int -> Int -> [Subst]
solveBCCond pfNames pfRules (NormalCond depth negated atom) currentW worlds worldNum bcDepth
  | negated =
      if null (solveBCCond pfNames pfRules (NormalCond depth False atom) currentW worlds worldNum bcDepth)
        then [emptySubst]
        else []
  | otherwise =
      let targetWorld = lookupWorld depth worlds worldNum currentW
          effectiveWorldNum = worldNum - depth
      in case targetWorld of
        Nothing ->
          []  -- past world doesn't exist
        Just tw
          | predName atom `Set.member` pfNames ->
              solveBackward pfNames pfRules atom tw worlds effectiveWorldNum (bcDepth + 1)
          | otherwise ->
              case evaluateExternal atom effectiveWorldNum of
                Just substs -> substs
                Nothing     -> matchInWorld atom tw

-- | Alpha-rename all variables in a rule to avoid capture.
--   Uses a prefix based on depth and rule index to generate unique names.
renameRuleVars :: Int -> Int -> NormalRule -> NormalRule
renameRuleVars depth idx rule =
  let prefix = "_bc" ++ show depth ++ "_" ++ show idx ++ "_"
      vars = Set.toList $ Set.union
               (fvAtom (nrHead rule))
               (Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule])
      renaming = Map.fromList [(v, TVar (prefix ++ v)) | v <- vars]
  in NormalRule
       { nrConditions = map (applySubstNormalCond renaming) (nrConditions rule)
       , nrHead = applySubstAtom renaming (nrHead rule)
       }

-- ============================================================
-- Stratification
-- ============================================================

-- | Partition rules into strata for negation-safe evaluation
stratify :: NormalProgram -> Either String [[NormalRule]]
stratify prog =
  case computeStrata prog of
    Left err -> Left err
    Right strataMap ->
      let maxStratum = if Map.null strataMap then 0
                       else maximum (Map.elems strataMap)
      in Right [filter (\r -> Map.findWithDefault 0 (predName (nrHead r)) strataMap == s) prog
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

computeStrata :: NormalProgram -> Either String (Map Name Int)
computeStrata prog =
  let deps = buildDeps prog
      allPreds = Set.toList $ Set.fromList $ map (predName . nrHead) prog
      initial = Map.fromList [(p, 0) | p <- allPreds]
  in fixStrata deps initial (length allPreds + 1)

fixStrata :: Map Name [(Name, DepKind)] -> Map Name Int -> Int -> Either String (Map Name Int)
fixStrata _ _ 0 = Left "Program is not stratifiable: negative dependency cycle detected"
fixStrata deps m fuel =
  let m' = Map.mapWithKey (updateStratum deps m) m
  in if m' == m then Right m else fixStrata deps m' (fuel - 1)

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

-- ============================================================
-- Tracing
-- ============================================================

-- | For each derived fact in the current world, return which rules derived it.
--   Uses provenance recorded during world computation rather than re-deriving.
traceDerivations :: InterpreterState -> [(GroundAtom, NormalRule)]
traceDerivations st =
  concatMap (\(atom, rules) -> map (\r -> (atom, r)) rules) (Map.toList (isTraces st))
