-- |
-- Module      : TemporalProlog.Interpreter
-- Description : Hybrid forward/backward-chaining execution engine (paper §5.2)
--
-- Executes a normalized Temporal Prolog program by computing a sequence
-- of worlds (sets of ground atoms). Each world is a least fixed point for a
-- condition-1 program or one of the paper's ordered minimal models otherwise,
-- with the following fixed inputs:
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
-- __Minimal models.__ Programs satisfying the paper's condition 1 use a
-- stratified least-fixed-point fast path.  Finite programs with recursion
-- through current-world negation are evaluated by enumerating the candidate
-- base and selecting the paper's SCC-lexicographic minimal models.  The
-- dependency graph excludes conditions with @\@-depth > 0@ because those
-- reference already-computed past worlds.
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
  , stepWorldAll
  , stepWorldGeneralAll
  , stepWorldStratified
  , stepWorldN
  , assertFact
  , assertFactEither
  , queryAtom
  , queryAtomEither
  , worldMatches
  , currentWorld
  , getHistory
  , getWorldNumber
  , traceDerivations
  ) where

import Control.Monad (guard)
import Data.Graph (SCC(..), stronglyConnComp)
import Data.List (partition, sort, sortOn)
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

-- | Checked assertion API for conformance-sensitive callers.  The legacy
-- 'assertFact' constructor remains source compatible, but 'stepWorld' also
-- rejects any non-ground assertion before it can enter a world.
assertFactEither :: GroundAtom -> InterpreterState -> Either String InterpreterState
assertFactEither atom state
  | isGroundAtom atom = Right (assertFact atom state)
  | otherwise = Left "Asserted facts must be ground (no variables)"

-- | Query whether an atom matches anything in the current world.
--   For pattern-function predicates, dispatches to the backward chainer
--   since PF atoms are never stored in the world set.
queryAtom :: Atom -> InterpreterState -> [Subst]
queryAtom pat st = either (const []) id (queryAtomEither pat st)

-- | Query with resource errors preserved.  The legacy 'queryAtom' wrapper
-- maps errors to no answers for API compatibility; conformance-sensitive
-- callers MUST use this function.
queryAtomEither :: Atom -> InterpreterState -> Either String [Subst]
queryAtomEither pat st =
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
     else Right $ case currentWorld st of
            Nothing -> []
            Just w  -> matchInWorld pat w

-- | Test whether an atom pattern matches a stored fact in a world.  Unlike
-- 'queryAtomEither', this never invokes pattern-function relations.
worldMatches :: Atom -> World -> Bool
worldMatches patternAtom = not . null . matchInWorld patternAtom

-- | Advance the interpreter by one world
stepWorld :: InterpreterState -> Either String InterpreterState
stepWorld st = do
  states <- stepWorldAll st
  case states of
    [] -> Left "World computation produced no minimal model"
    -- Execution may select any minimal model.  Selecting the first
    -- canonical world makes the convenience API reproducible.
    states' -> Right (head (sortOn (worldToSet . currentWorldOrEmpty) states'))

-- | Advance through every minimal current-world model.  A caller that needs
-- to preserve nondeterminism can branch on the returned states.
stepWorldAll :: InterpreterState -> Either String [InterpreterState]
stepWorldAll = stepWorldWith computeWorldAll

-- | Force the finite general evaluator, including on condition-1 programs.
-- This is exported so conformance tests can compare it with the fast path.
stepWorldGeneralAll :: InterpreterState -> Either String [InterpreterState]
stepWorldGeneralAll = stepWorldWith computeWorldGeneral

-- | Force the paper's condition-1 least-fixed-point evaluator.
stepWorldStratified :: InterpreterState -> Either String InterpreterState
stepWorldStratified st = do
  states <- stepWorldWith computeWorldStratified st
  case states of
    [st'] -> Right st'
    _ -> Left "Internal error: stratified evaluator did not return one world"

currentWorldOrEmpty :: InterpreterState -> World
currentWorldOrEmpty = fromMaybe emptyWorld . currentWorld

type WorldComputer = NormalProgram -> Set Name -> IntMap World -> World -> Int
                  -> Either String [(World, Map GroundAtom [NormalRule])]

stepWorldWith :: WorldComputer -> InterpreterState -> Either String [InterpreterState]
stepWorldWith computer st =
  let worldNum = case isWorldNum st of
        Nothing -> 0
        Just n  -> n + 1
      worlds = isWorlds st
      assertions = worldFromList (isAssertions st)
      prog = isProgram st
      pfNames = isPFNames st
  in do
    if all isGroundAtom (isAssertions st)
      then Right ()
      else Left "Asserted facts must be ground (no variables)"
    validateExecutableProfile prog pfNames
    computed <- computer prog pfNames worlds assertions worldNum
    Right
      [ st { isWorlds     = IntMap.insert worldNum newWorld worlds
           , isWorldNum   = Just worldNum
           , isAssertions = []
           , isTraces     = traces
           }
      | (newWorld, traces) <- computed
      ]

-- | Step N worlds
stepWorldN :: Int -> InterpreterState -> Either String InterpreterState
stepWorldN n _ | n < 0 = Left "Step count must be non-negative"
stepWorldN 0 st = Right st
stepWorldN n st = case stepWorld st of
  Left err -> Left err
  Right st' -> stepWorldN (n-1) st'

-- | Select the optimized condition-1 evaluator where possible and the
-- finite minimal-model evaluator otherwise.
computeWorldAll :: WorldComputer
computeWorldAll prog pfNames worlds assertions worldNum =
  let (_, fcRules) = partition (\r -> predName (nrHead r) `Set.member` pfNames) prog
  in case stratify fcRules of
       Right _ -> computeWorldStratified prog pfNames worlds assertions worldNum
       Left _  -> computeWorldGeneral prog pfNames worlds assertions worldNum

-- | Compute the unique condition-1 world by stratified fixed points.
computeWorldStratified :: WorldComputer
computeWorldStratified prog pfNames worlds assertions worldNum =
  let -- Partition rules: PF-defining rules go to backward chainer,
      -- forward-chaining rules go through stratification
      (pfRules, fcRules) = partition (\r -> predName (nrHead r) `Set.member` pfNames) prog
      -- Process each stratum in order, accumulating the world
      initialWorld = assertions `worldUnion` externalFacts worldNum
  in case stratify fcRules of
    Left err -> Left err
    Right strata ->
      fmap (:[]) $ foldl (\acc stratumRules -> do
              (w, ts) <- acc
              (w', ts') <- processStratum pfNames pfRules worlds worldNum w stratumRules
              Right (w', Map.unionWith (++) ts ts'))
            (Right (initialWorld, Map.empty))
            strata

-- | Maximum number of non-fixed candidate atoms accepted by exhaustive
-- minimal-model enumeration.  The limit makes resource exhaustion explicit
-- rather than silently changing the program's semantics.
maxModelCandidateAtoms :: Int
maxModelCandidateAtoms = 20

-- | Compute every SCC-lexicographic minimal model of a finite current world.
computeWorldGeneral :: WorldComputer
computeWorldGeneral prog pfNames worlds assertions worldNum = do
  let (pfRules, fcRules) = partition (\r -> predName (nrHead r) `Set.member` pfNames) prog
      fixedWorld = assertions `worldUnion` externalFacts worldNum
      relaxedRules = map relaxCurrentNegation fcRules
  candidateWorld <- candidateFixedPoint
    pfNames pfRules fcRules relaxedRules worlds worldNum fixedWorld
  let fixedAtoms = worldToSet fixedWorld
      candidates = sort . Set.toList $
        worldToSet candidateWorld `Set.difference` fixedAtoms
      candidateCount = length candidates
  if candidateCount > maxModelCandidateAtoms
    then Left $ "Minimal-model candidate base has " ++ show candidateCount
             ++ " atoms, exceeding the configured limit of "
             ++ show maxModelCandidateAtoms
    else do
      let proposed =
            [ worldFromSet (fixedAtoms `Set.union` Set.fromList subset)
            | subset <- powerSet candidates
            ]
      modelFlags <- mapM
        (isModel pfNames pfRules fcRules worlds worldNum) proposed
      let models = [w | (w, True) <- zip proposed modelFlags]
          components = orderedPredicateSCCs fcRules
          minimals = filter (isMinimal components models) models
      if null models
        then Left "Program has no model for the current external interpretation"
        else mapM
          (\w -> do
              traces <- tracesForModel pfNames pfRules fcRules worlds worldNum w
              Right (w, traces))
          (sortOn worldToSet minimals)

-- A negated current-world condition constrains which candidate subsets are
-- models, but cannot safely restrict the candidate Herbrand base itself.
relaxCurrentNegation :: NormalRule -> NormalRule
relaxCurrentNegation rule = rule
  { nrConditions = filter (not . isCurrentNegated) (nrConditions rule) }
  where
    isCurrentNegated c = ncPrevDepth c == 0 && ncNegated c

candidateFixedPoint
  :: Set Name -> [NormalRule] -> [NormalRule] -> [NormalRule]
  -> IntMap World -> Int -> World
  -> Either String World
candidateFixedPoint pfNames pfRules originalRules relaxedRules worlds worldNum =
  go maxFixedPointIterations
  where
    internalNames = Set.fromList (map (predName . nrHead) originalRules)
    go 0 _ = Left $ "Candidate generation did not converge within "
                   ++ show maxFixedPointIterations ++ " iterations at world "
                   ++ show worldNum
    go fuel w = do
      (derivedWorld, _) <- applyRulesOnce
        pfNames pfRules relaxedRules worlds worldNum w
      blockers <- concat <$> mapM (groundNegativeCandidates derivedWorld) originalRules
      let w' = foldl (flip worldInsert) derivedWorld blockers
      if w' == w then Right w else go (fuel - 1) w'

    -- Classical minimal models may contain an unsupported atom solely to
    -- make a negative antecedent false (paper Section 4.7 does exactly this).
    -- Ground every such internal atom under the relaxed positive closure so
    -- exhaustive enumeration does not silently impose supported/stable-model
    -- semantics.
    groundNegativeCandidates w rule = do
      let relaxedConds = nrConditions (relaxCurrentNegation rule)
          negativeConds =
            [ cond
            | cond <- nrConditions rule
            , ncPrevDepth cond == 0
            , ncNegated cond
            , predName (ncAtom cond) `Set.member` internalNames
            ]
      substs <- findSatisfyingSubsts
        pfNames pfRules relaxedConds worlds worldNum w
      Right
        [ atom
        | subst <- substs
        , cond <- negativeConds
        , let atom = applySubstAtom subst (ncAtom cond)
        , isGroundAtom atom
        ]

powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = let rest = powerSet xs in rest ++ map (x:) rest

isModel
  :: Set Name -> [NormalRule] -> [NormalRule] -> IntMap World -> Int -> World
  -> Either String Bool
isModel pfNames pfRules rules worlds worldNum world = do
  satisfied <- mapM ruleSatisfied rules
  Right (and satisfied)
  where
    ruleSatisfied rule = do
      derived <- deriveFromRule pfNames pfRules rule worlds worldNum world
      Right (all (`worldMember` world) derived)

tracesForModel
  :: Set Name -> [NormalRule] -> [NormalRule] -> IntMap World -> Int -> World
  -> Either String (Map GroundAtom [NormalRule])
tracesForModel pfNames pfRules rules worlds worldNum world = do
  derivations <- mapM
    (\rule -> do
       atoms <- deriveFromRule pfNames pfRules rule worlds worldNum world
       Right [(atom, [rule]) | atom <- atoms, worldMember atom world])
    rules
  Right (Map.fromListWith (++) (concat derivations))

isMinimal :: [Set Name] -> [World] -> World -> Bool
isMinimal components models model =
  not (any (\other -> other /= model && modelSmaller components other model) models)

-- The paper compares SCCs in dependency-first order.  At the first unequal
-- component, a proper subset is smaller; incomparable sets remain so.
modelSmaller :: [Set Name] -> World -> World -> Bool
modelSmaller [] _ _ = False
modelSmaller (component:rest) left right =
  let select w = Set.filter
        (\a -> predName a `Set.member` component)
        (worldToSet w)
      l = select left
      r = select right
  in if l == r
       then modelSmaller rest left right
       else l `Set.isProperSubsetOf` r

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
    go fuel w ts = do
      (w', newTraces) <- applyRulesOnce pfNames pfRules rules worlds worldNum w
      if w' == w then Right (w, ts) else go (fuel - 1) w' (Map.unionWith (++) ts newTraces)

-- | Apply all rules once, returning the union of derived facts with the current world
--   and traces for newly derived facts.
applyRulesOnce :: Set Name -> [NormalRule] -> [NormalRule] -> IntMap World -> Int -> World
               -> Either String (World, Map GroundAtom [NormalRule])
applyRulesOnce pfNames pfRules rules worlds worldNum world = do
  ruleDerivations <- mapM
    (\r -> map (\a -> (a, r)) <$> deriveFromRule pfNames pfRules r worlds worldNum world)
    rules
  let derivations = concat ruleDerivations
      newWorld = foldl (\w (a, _) -> worldInsert a w) world derivations
      -- Only trace newly derived facts (not already in world)
      newTraces = Map.fromListWith (++)
        [(a, [r]) | (a, r) <- derivations, not (worldMember a world)]
  Right (newWorld, newTraces)

-- | Derive all possible ground atoms from a single rule
deriveFromRule :: Set Name -> [NormalRule] -> NormalRule -> IntMap World -> Int -> World
               -> Either String [GroundAtom]
deriveFromRule pfNames pfRules (NormalRule conds headAtom) worlds worldNum world = do
  -- Find all substitutions that satisfy all conditions.
  substs <- findSatisfyingSubsts pfNames pfRules conds worlds worldNum world
  let
      -- Apply each substitution to the head
      heads = map (\s -> applySubstAtom s headAtom) substs
      -- Only keep ground results
  Right (filter isGroundAtom heads)

-- | Find all substitutions satisfying a list of conditions.
--   Reorders so positive conditions are processed before negative ones
--   (standard safety condition for negation-as-failure).
findSatisfyingSubsts :: Set Name -> [NormalRule] -> [NormalCond] -> IntMap World -> Int -> World
                     -> Either String [Subst]
findSatisfyingSubsts pfNames pfRules conds worlds worldNum world =
  let (pos, neg) = partition (\c -> not (ncNegated c)) conds
      ordered = pos ++ neg
  in go ordered worlds worldNum world
  where
    go [] _ _ _ = Right [emptySubst]
    go (c:cs) ws wn w = do
      first <- satisfyCond pfNames pfRules c ws wn w
      branches <- mapM (continue cs ws wn w) first
      Right (concat branches)
    continue cs ws wn w s1 = do
      let cs' = map (applySubstNormalCond s1) cs
      rest <- go cs' ws wn w
      Right [composeSubst s2 s1 | s2 <- rest]

-- | Find all substitutions that satisfy a single normal condition
satisfyCond :: Set Name -> [NormalRule] -> NormalCond -> IntMap World -> Int -> World
            -> Either String [Subst]
satisfyCond pfNames pfRules (NormalCond depth negated atom) worlds worldNum world =
  let targetWorld = lookupWorld depth worlds worldNum world
  in case targetWorld of
    Nothing ->
      -- Paper section 5.2: @F is false at world 0 regardless of F.  In
      -- normal form the negation is inside the @ operators, so @~F is also
      -- false when the referenced world does not exist.  An outer ~@F is
      -- eliminated with an auxiliary predicate during normalization.
      Right []
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
satisfyPositive :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int
                -> Either String [Subst]
satisfyPositive pfNames pfRules pat world worlds worldNum =
  -- Check external predicates first
  case evaluateExternal pat worldNum of
    Just substs -> Right substs
    Nothing
      -- If this is a pattern-function predicate, use backward chaining
      | predName pat `Set.member` pfNames ->
          solveBackward pfNames pfRules pat world worlds worldNum 0
      | otherwise -> Right (matchInWorld pat world)

-- | Match a pattern atom against all atoms in a world with matching predicate.
matchInWorld :: Atom -> World -> [Subst]
matchInWorld pat w =
  let candidates = worldLookupPred (predName pat) w
  in mapMaybe (matchAtom pat) (Set.toList candidates)

-- | Find substitutions for a negated atom (negation-as-failure)
satisfyNegated :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> World -> Int
               -> Either String [Subst]
satisfyNegated pfNames pfRules atom targetWorld worlds _currentWorld worldNum =
  -- For negation-as-failure: ~p(X) is true if there is no instance of p in the world.
  -- For PF predicates we must always consult the backward chainer, since PF atoms
  -- are never stored in the world set.
  if isGroundAtom atom && not (predName atom `Set.member` pfNames)
    then Right $ if not (worldMember atom targetWorld) && null (fromMaybe [] (evaluateExternal atom worldNum))
         then [emptySubst]
         else []
    else do
      -- For non-ground atoms or PF predicates, check via satisfyPositive
      -- (which dispatches to backward chaining for PF predicates).
      positive <- satisfyPositive pfNames pfRules atom targetWorld worlds worldNum
      Right $ if null positive then [emptySubst] else []

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
solveBackward :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int -> Int
              -> Either String [Subst]
solveBackward _pfNames _pfRules _goal _world _worlds _worldNum depth
  | depth >= maxBCDepth = Left $ "Pattern-function recursion exceeded the configured depth limit of "
                               ++ show maxBCDepth
solveBackward pfNames pfRules goal world worlds worldNum depth = do
  answers <- mapM
    (\(i, rule) -> tryBCRule pfNames pfRules goal world worlds worldNum depth i rule)
    (zip [0..] pfRules)
  Right (concat answers)

-- | Try to use a single PF rule to satisfy a goal.
--   Alpha-renames the rule, unifies its head with the goal, then solves conditions.
tryBCRule :: Set Name -> [NormalRule] -> Atom -> World -> IntMap World -> Int -> Int -> Int
          -> NormalRule -> Either String [Subst]
tryBCRule pfNames pfRules goal world worlds worldNum depth idx rule =
  let renamedRule = renameRuleVars depth idx rule
      rHead = nrHead renamedRule
      rConds = nrConditions renamedRule
  in case unifyAtom goal rHead of
    Nothing -> Right []
    Just s -> do
      let conds' = map (applySubstNormalCond s) rConds
      solved <- solveBCConds pfNames pfRules conds' world worlds worldNum depth
      Right (map (\s2 -> composeSubst s2 s) solved)

-- | Solve a list of conditions sequentially, threading substitutions.
solveBCConds :: Set Name -> [NormalRule] -> [NormalCond] -> World -> IntMap World -> Int -> Int
             -> Either String [Subst]
solveBCConds _pfNames _pfRules [] _world _worlds _worldNum _depth = Right [emptySubst]
solveBCConds pfNames pfRules (c:cs) world worlds worldNum depth = do
  first <- solveBCCond pfNames pfRules c world worlds worldNum depth
  branches <- mapM continue first
  Right (concat branches)
  where
    continue s1 = do
      let cs' = map (applySubstNormalCond s1) cs
      rest <- solveBCConds pfNames pfRules cs' world worlds worldNum depth
      Right [composeSubst s2 s1 | s2 <- rest]

-- | Solve a single condition in backward-chaining context.
--   PF predicates recurse; others fall back to world lookup.
--   Respects @-depth by looking up the appropriate past world.
solveBCCond :: Set Name -> [NormalRule] -> NormalCond -> World -> IntMap World -> Int -> Int
            -> Either String [Subst]
solveBCCond pfNames pfRules (NormalCond depth negated atom) currentW worlds worldNum bcDepth =
  let targetWorld = lookupWorld depth worlds worldNum currentW
      effectiveWorldNum = worldNum - depth
  in case targetWorld of
    -- As in forward evaluation, @F is false at world 0 even when F is
    -- negated.  The normalizer represents an outer ~@F with an auxiliary.
    Nothing -> Right []
    Just tw
      | negated -> do
          positive <- solveBCCond pfNames pfRules
            (NormalCond depth False atom)
            currentW worlds worldNum bcDepth
          Right $ if null positive then [emptySubst] else []
      | predName atom `Set.member` pfNames ->
          solveBackward pfNames pfRules atom tw worlds effectiveWorldNum (bcDepth + 1)
      | otherwise ->
          case evaluateExternal atom effectiveWorldNum of
            Just substs -> Right substs
            Nothing     -> Right (matchInWorld atom tw)

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
-- Executable-profile validation
-- ============================================================

-- | Forward rules must be range restricted.  PF-defining clauses are
-- relational and are checked dynamically by ground callers instead.
validateExecutableProfile :: NormalProgram -> Set Name -> Either String ()
validateExecutableProfile prog pfNames = mapM_ validateRule fcRules
  where
    fcRules = filter (\r -> predName (nrHead r) `Set.notMember` pfNames) prog
    validateRule rule =
      let positives = filter (not . ncNegated) (nrConditions rule)
          bound = bindingFixedPoint positives
          observed = Set.union
            (fvAtom (nrHead rule))
            (Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, ncNegated c])
          unsafe = observed `Set.difference` bound
      in if Set.null unsafe
           then Right ()
           else Left $ "Rule is outside the range-restricted executable profile; "
                    ++ "variable(s) " ++ show (Set.toList unsafe)
                    ++ " are observed before being grounded: " ++ show rule

bindingFixedPoint :: [NormalCond] -> Set Var
bindingFixedPoint conds = go Set.empty
  where
    go bound =
      let bound' = foldl bindFromCondition bound conds
      in if bound' == bound then bound else go bound'

bindFromCondition :: Set Var -> NormalCond -> Set Var
bindFromCondition bound cond = case ncAtom cond of
  Atom "true" [] -> bound
  Atom "false" [] -> bound
  Atom "=" [left, right] -> bindEquality bound left right
  Atom "is" [result, expr]
    | fvTerm expr `Set.isSubsetOf` bound -> Set.union bound (fvTerm result)
    | otherwise -> bound
  Atom op _ | op `elem` [">", "<", ">=", "<="] -> bound
  -- A successful at/1 call and a successful world/PF relation lookup bind
  -- every variable in the matched atom to a ground term in this profile.
  atom -> Set.union bound (fvAtom atom)

bindEquality :: Set Var -> Term -> Term -> Set Var
bindEquality bound left right =
  let leftVars = fvTerm left
      rightVars = fvTerm right
      boundLeft = leftVars `Set.isSubsetOf` bound
      boundRight = rightVars `Set.isSubsetOf` bound
      withRight = if boundLeft then Set.union bound rightVars else bound
  in if boundRight then Set.union withRight leftVars else withRight

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

-- | Predicate SCCs in a deterministic dependency-first linear extension.
-- Edges are stored consumer-to-dependency, so repeatedly removing sink SCCs
-- yields the required order.
orderedPredicateSCCs :: NormalProgram -> [Set Name]
orderedPredicateSCCs prog = order [] components
  where
    heads = Set.fromList (map (predName . nrHead) prog)
    deps = buildDeps prog
    graphNodes =
      [ (p, p, [q | (q, _) <- Map.findWithDefault [] p deps, q `Set.member` heads])
      | p <- Set.toList heads
      ]
    components = map sccSet (stronglyConnComp graphNodes)
    sccSet (AcyclicSCC p) = Set.singleton p
    sccSet (CyclicSCC ps) = Set.fromList ps

    order acc [] = reverse acc
    order acc remaining =
      let compOf p = nextComponent p remaining
          outgoing component = Set.fromList
            [ target
            | p <- Set.toList component
            , (q, _) <- Map.findWithDefault [] p deps
            , Just target <- [compOf q]
            , target /= component
            ]
          ready = sortOn Set.findMin
            [ component
            | component <- remaining
            , Set.null (outgoing component)
            ]
          remaining' = filter (`notElem` ready) remaining
      in if null ready
           -- stronglyConnComp already collapsed cycles; this is defensive.
           then reverse acc ++ sortOn Set.findMin remaining
           else order (reverse ready ++ acc) remaining'

    nextComponent _ [] = Nothing
    nextComponent p (component:rest)
      | p `Set.member` component = Just component
      | otherwise = nextComponent p rest

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
