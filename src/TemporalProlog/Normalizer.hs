-- |
-- Module      : TemporalProlog.Normalizer
-- Description : Five-step normalization pipeline (paper §5.1, pp. 10–14)
--
-- Transforms user-level 'Rule's into 'NormalRule's suitable for the
-- world-by-world interpreter. The pipeline has five steps, each
-- eliminating a class of temporal operators by introducing auxiliary
-- predicates:
--
-- 1. __Step 1__ (p. 10): Eliminate future-time result operators —
--    'RAlways' (□), 'RUntil', 'RAtNext' — and split head/body
--    conjunctions.
--
-- 2. __Step 2__ (pp. 10–11): Eliminate past-time condition operators —
--    'CSince', 'CAfter', 'CFor', 'CHasBeen' (■), 'COnce' (◆).
--
-- 3. __Step 3__ (pp. 12–13): Expand pattern functions. First substep
--    converts @f(args) -> body@ definitions to predicate facts; second
--    substep replaces nested function calls in terms with fresh variables
--    and auxiliary conditions.
--
-- 4. __Step 4__ (p. 13): Push negation to the atomic level so that every
--    @~@ directly precedes an atom or @@^n(atom)@.
--
-- 5. __Step 5__ (p. 14): Distribute @\@@ over @/\\@ so each condition has
--    the canonical form @@^m(~?)atom@.
--
-- Each step iterates until a termination condition is met (the relevant
-- operator class is absent). The paper proves termination because each
-- step strictly decreases the count of its target operators.
module TemporalProlog.Normalizer
  ( normalize
  , step1
  , step2
  , eliminateTermPrev
  , eliminateTermPrevM
  , step3
  , step4
  , step5
  ) where

import Control.Monad (unless)
import Data.IORef
import Data.List (nub)
import qualified Data.Set as Set
import System.IO (hPutStrLn, stderr)
import TemporalProlog.PrettyPrint (ppNormalRule)
import TemporalProlog.Syntax

-- | Fresh name generation
type FreshM = IO

freshName :: IORef Int -> String -> FreshM Name
freshName ref prefix = do
  n <- readIORef ref
  writeIORef ref (n + 1)
  return (prefix ++ "_aux" ++ show n)

-- | Maximum iterations for normalizer fixed-point loops
maxNormalizerIterations :: Int
maxNormalizerIterations = 1000

-- | Flatten a rule with conjunction in the body into a list of conditions
flattenConds :: Cond -> [Cond]
flattenConds (CAnd cs) = concatMap flattenConds cs
flattenConds c = [c]

-- | Flatten a result with conjunction into a list of results
flattenResults :: Result -> [Result]
flattenResults (RAnd rs) = concatMap flattenResults rs
flattenResults r = [r]

resultVars :: Result -> [Var]
resultVars = Set.toList . fvResult

varsToTerms :: [Var] -> [Term]
varsToTerms = map TVar

-- ============================================================
-- Step 1: Eliminate always (□), until, atnext
-- Also split conjunctions in heads and bodies.
-- ============================================================

-- | Step 1: Eliminate □, until, atnext; split conjunctions (paper p. 10)
step1 :: IORef Int -> [Rule] -> FreshM [Rule]
step1 ref = go maxNormalizerIterations
  where
    go 0 _ = fail "Normalizer step 1 (eliminate always/until/atnext) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM (step1Rule ref) rules
      let rs' = concat rs
      if any needsStep1 rs'
        then go (fuel - 1) rs'
        else return rs'

needsStep1 :: Rule -> Bool
needsStep1 (Fact r) = needsStep1Result r
needsStep1 (Rule cs r) = needsStep1Result r || any hasNestedAnd cs

needsStep1Result :: Result -> Bool
needsStep1Result (RAlways _)    = True
needsStep1Result (RUntil _ _)   = True
needsStep1Result (RAtNext _ _)  = True
needsStep1Result (RAnd _)       = True
needsStep1Result (RNext _)      = True
needsStep1Result _              = False

hasNestedAnd :: Cond -> Bool
hasNestedAnd (CAnd _) = True
hasNestedAnd _ = False

step1Rule :: IORef Int -> Rule -> FreshM [Rule]
step1Rule ref rule = case rule of
  -- Split top-level conjunction in facts: q /\ s -> q, s
  Fact (RAnd rs) -> return [Fact r | r <- flattenResults (RAnd rs)]

  -- Split conjunction in implication head: a => q /\ s -> a => q, a => s
  Rule cs (RAnd rs) ->
    return [Rule cs r | r <- flattenResults (RAnd rs)]

  -- Flatten conjunction in body
  Rule cs r | any isCAnd cs -> do
    let cs' = concatMap flattenConds cs
    step1Rule ref (Rule cs' r)
    where isCAnd (CAnd _) = True
          isCAnd _ = False

  -- (2) □q -> q, @p(Xs) => p(Xs), p(Xs) => q
  Fact (RAlways q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName ref "always"
    let pAtom = Atom p vterms
    return [ Fact q
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           , Rule [CAtom pAtom] q
           ]

  -- a => □q  ->  a => p(Xs), @p(Xs) => p(Xs), p(Xs) => q
  Rule cs (RAlways q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName ref "always"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           , Rule [CAtom pAtom] q
           ]

  -- (3) q until a -> ~a => q  (also: a => q until b generates more rules)
  Fact (RUntil q a) ->
    return [ Rule [CNeg a] q ]

  Rule cs (RUntil q b) -> do
    let vs = Set.toList $ Set.union (fvResult q) (fvCond b)
        vterms = varsToTerms vs
    p <- freshName ref "until"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CNeg b] (RAtom pAtom)
           , Rule [CAtom pAtom, CNeg b] q
           ]

  -- (4) q atnext a -> a => q  (when bare)
  Fact (RAtNext _q _a) ->
    return [rule] -- bare atnext fact: unusual, pass through

  -- (4) a => q atnext b -> a => p(Xs), @p(Xs) /\ @~b => p(Xs), p(Xs) /\ b => q
  Rule cs (RAtNext q b) -> do
    let vs = Set.toList $ Set.union (fvResult q) (fvCond b)
        vterms = varsToTerms vs
    p <- freshName ref "atnext"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CPrev (CNeg b)] (RAtom pAtom)
           , Rule [CAtom pAtom, b] q
           ]

  -- next q  ->  p(Xs).  @p(Xs) => q.
  Fact (RNext q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName ref "next"
    let pAtom = Atom p vterms
    return [ Fact (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] q
           ]

  -- a => next q  ->  a => p(Xs).  @p(Xs) => q.
  Rule cs (RNext q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName ref "next"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] q
           ]

  -- Base case: no transformation needed
  _ -> return [rule]

-- ============================================================
-- Step 2: Eliminate since, after, for, has-been (#), once (?)
-- ============================================================

-- | Step 2: Eliminate since, after, for, ■, ◆ (paper pp. 10–11)
step2 :: IORef Int -> [Rule] -> FreshM [Rule]
step2 ref = go maxNormalizerIterations
  where
    go 0 _ = fail "Normalizer step 2 (eliminate since/after/for/has-been/once) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM (step2Rule ref) rules
      let rs' = concat rs
      if any needsStep2 rs'
        then go (fuel - 1) rs'
        else return rs'

needsStep2 :: Rule -> Bool
needsStep2 (Fact _) = False  -- facts at this point should be atoms
needsStep2 (Rule cs _) = any hasStep2Op cs

hasStep2Op :: Cond -> Bool
hasStep2Op (CHasBeen _)  = True
hasStep2Op (COnce _)     = True
hasStep2Op (CSince _ _)  = True
hasStep2Op (CAfter _ _)  = True
hasStep2Op (CFor _ _)    = True
hasStep2Op (CEventually _) = True
hasStep2Op (CNeg c)      = hasStep2Op c
hasStep2Op (CPrev c)     = hasStep2Op c
hasStep2Op (CAnd cs)     = any hasStep2Op cs
hasStep2Op _             = False

step2Rule :: IORef Int -> Rule -> FreshM [Rule]
step2Rule ref rule@(Rule cs r) = case findStep2 cs of
  Nothing -> return [rule]
  Just (before, op, after_) -> do
    extras <- transformStep2 ref op r (before ++ after_)
    return extras
step2Rule _ rule = return [rule]

-- Find first condition that needs step 2 transformation
findStep2 :: [Cond] -> Maybe ([Cond], Cond, [Cond])
findStep2 = go []
  where
    go _ [] = Nothing
    go acc (c:cs)
      | hasStep2Op c = Just (reverse acc, c, cs)
      | otherwise    = go (c:acc) cs

transformStep2 :: IORef Int -> Cond -> Result -> [Cond] -> FreshM [Rule]
transformStep2 ref cond r otherConds = case cond of
  -- (1) ...■a... => r  ->  ...p(Xs)... => r, a /\ at(0) => p(Xs), @p(Xs) /\ a => p(Xs)
  CHasBeen a -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "hasbeen"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a, CAtom (Atom "at" [TFun "0" []])] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]

  -- (2) ...◆a... => r  ->  ...p(Xs)... => r, a => p(Xs), @p(Xs) => p(Xs)
  COnce a -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "once"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           ]

  -- (3) ...a since b... => r -> ...p(Xs)... => r, b /\ a => p(Xs), @p(Xs) /\ a => p(Xs)
  CSince a b -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, fvCond b, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "since"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [b, a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]

  -- (4) ...a after b... => r -> ...p(Xs)... => r, a => p(Xs), @p(Xs) /\ ~b => p(Xs)
  CAfter a b -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, fvCond b, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "after"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CNeg b] (RAtom pAtom)
           ]

  -- eventually is a synonym for once
  CEventually a -> transformStep2 ref (COnce a) r otherConds

  -- (5) ...a for n... => r -> ...(a /\ @a /\ @@a /\ ... /\ @^(n-1)a)... => r
  CFor a n -> do
    let expanded = [nestPrev i a | i <- [0..n-1]]
    return [Rule (expanded ++ otherConds) r]

  -- Recurse into negation - but step 2 shouldn't have negation wrapping these
  -- Actually it can: e.g. ~#a. We handle by introducing auxiliary.
  CNeg inner | hasStep2Op inner -> do
    let allVars = Set.toList $ Set.unions
          [fvCond inner, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "neg"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    -- inner => p(Xs), then use ~p(Xs) instead
    innerRules <- transformStep2 ref inner (RAtom pAtom) []
    return $ Rule (CNeg pCond : otherConds) r : innerRules

  -- For conditions wrapped in @, we need to handle them too
  CPrev inner | hasStep2Op inner -> do
    -- We can't easily handle @ wrapping step2 ops directly.
    -- Best approach: extract the inner, create auxiliary, wrap with @
    let allVars = Set.toList $ Set.unions
          [fvCond inner, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName ref "prev"
    let pAtom = Atom p vterms
        pCond = CPrev (CAtom pAtom)
    innerRules <- transformStep2 ref inner (RAtom pAtom) []
    return $ Rule (pCond : otherConds) r : innerRules

  _ -> return [Rule (cond : otherConds) r]

nestPrev :: Int -> Cond -> Cond
nestPrev 0 c = c
nestPrev n c = CPrev (nestPrev (n-1) c)

-- ============================================================
-- Eliminate term-level TPrev by converting to condition-level CPrev
-- After this pass, no Term contains TPrev.
-- ============================================================

-- | Eliminate TPrev from terms by converting to condition-level CPrev.
-- For each atom, if all terms have the same outermost TPrev depth,
-- strip the TPrevs and wrap the condition in that many CPrev layers.
-- Mixed depths within a single atom are decomposed into auxiliary
-- predicates that project argument subsets at each distinct depth.
--
-- Pure version (legacy): errors on mixed depths.
eliminateTermPrev :: [Rule] -> [Rule]
eliminateTermPrev = map eliminateTermPrevRule

eliminateTermPrevRule :: Rule -> Rule
eliminateTermPrevRule (Fact (RAtom a)) =
  case maxTermPrevInAtom a of
    0 -> Fact (RAtom a)
    _ -> error $ "TPrev in head atom not allowed: " ++ show a
eliminateTermPrevRule (Fact r) = Fact r
eliminateTermPrevRule (Rule conds result) =
  case result of
    RAtom a | maxTermPrevInAtom a > 0 ->
      error $ "TPrev in head atom not allowed: " ++ show a
    _ -> Rule (map liftTermPrev conds) result

-- | For a condition, find TPrev in its atom terms and lift to CPrev.
-- Pure version: errors on mixed depths.
liftTermPrev :: Cond -> Cond
liftTermPrev (CAtom (Atom name terms)) =
  let depths = map termPrevDepth terms
      maxD = maximum (0 : depths)
  in if maxD == 0
     then CAtom (Atom name terms)
     else if all (== maxD) depths
          then let terms' = map (stripTermPrevN maxD) terms
               in nestCPrev maxD (CAtom (Atom name terms'))
          else error $ "Mixed TPrev depths in atom not supported: " ++
                       show (Atom name terms) ++
                       " (depths: " ++ show depths ++ ")"
liftTermPrev (CPrev c) = CPrev (liftTermPrev c)
liftTermPrev (CNeg c) = CNeg (liftTermPrev c)
liftTermPrev (CAnd cs) = CAnd (map liftTermPrev cs)
liftTermPrev c = c

-- | Monadic version: handles mixed TPrev depths by decomposing into
-- auxiliary predicates. Returns the transformed rules plus any new
-- auxiliary rules needed for projection.
eliminateTermPrevM :: IORef Int -> [Rule] -> IO [Rule]
eliminateTermPrevM ref rules = do
  results <- mapM (eliminateTermPrevRuleM ref) rules
  return (concat results)

eliminateTermPrevRuleM :: IORef Int -> Rule -> IO [Rule]
eliminateTermPrevRuleM _ (Fact (RAtom a)) =
  case maxTermPrevInAtom a of
    0 -> return [Fact (RAtom a)]
    _ -> error $ "TPrev in head atom not allowed: " ++ show a
eliminateTermPrevRuleM _ (Fact r) = return [Fact r]
eliminateTermPrevRuleM ref (Rule conds result) =
  case result of
    RAtom a | maxTermPrevInAtom a > 0 ->
      error $ "TPrev in head atom not allowed: " ++ show a
    _ -> do
      results <- mapM (liftTermPrevM ref) conds
      let (conds', ruleLists) = unzip results
      return (Rule conds' result : concat ruleLists)

-- | Monadic version of liftTermPrev: returns the transformed condition
-- plus any auxiliary rules needed for mixed-depth decomposition.
liftTermPrevM :: IORef Int -> Cond -> IO (Cond, [Rule])
liftTermPrevM ref (CAtom (Atom name terms)) = do
  let depths = map termPrevDepth terms
      maxD = maximum (0 : depths)
  if maxD == 0
    then return (CAtom (Atom name terms), [])
    else if all (== maxD) depths
      then let terms' = map (stripTermPrevN maxD) terms
           in return (nestCPrev maxD (CAtom (Atom name terms')), [])
      else decomposeMixedDepths ref name terms depths
liftTermPrevM ref (CPrev c) = do
  (c', rules) <- liftTermPrevM ref c
  return (CPrev c', rules)
liftTermPrevM ref (CNeg c) = do
  (c', rules) <- liftTermPrevM ref c
  return (CNeg c', rules)
liftTermPrevM ref (CAnd cs) = do
  results <- mapM (liftTermPrevM ref) cs
  let (cs', ruleLists) = unzip results
  return (CAnd cs', concat ruleLists)
liftTermPrevM _ c = return (c, [])

-- | Decompose an atom with mixed TPrev depths into a conjunction of
-- conditions at different depths, plus auxiliary projection rules.
--
-- For example, @p(\@X, Y)@ with depths [1, 0] becomes:
--   - Main condition: @p(X, Y)@ (all TPrevs stripped, at depth 0)
--   - Auxiliary condition: @\@p_d1_auxN(X)@ (depth-1 args checked at previous world)
--   - Auxiliary rule: @p(A, B) => p_d1_auxN(A).@ (projects depth-1 arg positions)
--
-- If the minimum depth is > 0, we first strip that minimum from all terms
-- and wrap the entire result in that many CPrev layers.
decomposeMixedDepths :: IORef Int -> Name -> [Term] -> [Int] -> IO (Cond, [Rule])
decomposeMixedDepths ref name terms depths = do
  let minD = minimum depths
      -- Strip minD from all terms, reducing minimum depth to 0
      adjusted = map (\t -> stripTermPrevN minD t) terms
      adjustedDepths = map (\d -> d - minD) depths

  if all (== 0) adjustedDepths
    -- After stripping, all depths are uniform (shouldn't happen for mixed, but handle it)
    then return (nestCPrev minD (CAtom (Atom name adjusted)), [])
    else do
      -- Now minimum adjusted depth is 0, and some are > 0.
      -- Group args by their adjusted depth.
      let indexed = zip3 [0..] adjusted adjustedDepths
          nonZeroDs = nub $ filter (> 0) adjustedDepths

      auxResults <- mapM (\d -> do
            -- Indices with this adjusted depth
            let indicesAtD = [i | (i, _, dd) <- indexed, dd == d]
                -- Strip remaining d levels from those terms to get base terms
                strippedTerms = [stripTermPrevN d (adjusted !! i) | i <- indicesAtD]
            auxName <- freshName ref (name ++ "_d" ++ show d)
            -- Auxiliary condition: check these args at depth d
            let auxCond = nestCPrev d (CAtom (Atom auxName strippedTerms))
            -- Auxiliary projection rule: from the original predicate, project these positions
            -- Use fresh variables for all positions of the original predicate
            let freshVars = [TVar ("_TP" ++ show i) | i <- [0..length terms - 1]]
                projArgs = [freshVars !! i | i <- indicesAtD]
                auxRule = Rule [CAtom (Atom name freshVars)] (RAtom (Atom auxName projArgs))
            return (auxCond, auxRule)
          ) nonZeroDs

      -- Build the main condition with all TPrevs fully stripped (base terms)
      let baseTerms = [stripTermPrevN d t | (_, t, d) <- indexed]
          mainCond = CAtom (Atom name baseTerms)
          -- Combine: main condition + all auxiliary conditions
          allConds = mainCond : map fst auxResults
          combined = CAnd allConds
          -- Wrap everything in the minimum depth
          wrappedCond = nestCPrev minD combined
          allRules = map snd auxResults
      return (wrappedCond, allRules)

-- | Get the outermost TPrev depth of a term
termPrevDepth :: Term -> Int
termPrevDepth (TPrev t) = 1 + termPrevDepth t
termPrevDepth _ = 0

-- | Get max TPrev depth across all terms in an atom (including nested in TFun)
maxTermPrevInAtom :: Atom -> Int
maxTermPrevInAtom (Atom _ terms) = maximum (0 : map maxTermPrevInTerm terms)

-- | Get max TPrev depth anywhere in a term (including inside TFun)
maxTermPrevInTerm :: Term -> Int
maxTermPrevInTerm (TPrev t) = 1 + maxTermPrevInTerm t
maxTermPrevInTerm (TFun _ ts) = maximum (0 : map maxTermPrevInTerm ts)
maxTermPrevInTerm _ = 0

-- | Strip n layers of TPrev from a term
stripTermPrevN :: Int -> Term -> Term
stripTermPrevN 0 t = t
stripTermPrevN n (TPrev t) = stripTermPrevN (n-1) t
stripTermPrevN _ t = t

-- | Wrap a condition in n layers of CPrev
nestCPrev :: Int -> Cond -> Cond
nestCPrev 0 c = c
nestCPrev n c = CPrev (nestCPrev (n-1) c)

-- ============================================================
-- Step 3: Expand pattern functions
-- (Simplified: we convert pattern func defs into predicate rules)
-- ============================================================

-- | Step 3: Expand pattern functions (paper pp. 12–13)
step3 :: IORef Int -> [PatternFunc] -> [Rule] -> FreshM [Rule]
step3 _ [] rules = return rules
step3 ref pfs rules = do
  -- First substep: convert f(t1,...,tk) -> t0 into f(t1,...,tk,t0) predicate
  let pfRules = map patternFuncToRule pfs
      pfNames = Set.fromList [n | PatternFunc n _ _ <- pfs]
  -- Second substep: expand function calls in terms within rules
  rules' <- expandRulesFixpoint ref pfNames rules
  return (pfRules ++ rules')

patternFuncToRule :: PatternFunc -> Rule
patternFuncToRule (PatternFunc f args body) =
  Fact (RAtom (Atom f (args ++ [body])))

-- Iterate expansion until no pattern function calls remain in any rule
expandRulesFixpoint :: IORef Int -> Set.Set Name -> [Rule] -> FreshM [Rule]
expandRulesFixpoint ref pfNames rules = do
  results <- mapM (expandRule ref pfNames) rules
  let (rules', changed) = unzip results
  if or changed
    then expandRulesFixpoint ref pfNames rules'
    else return rules'

-- Expand one rule: walk all terms, replace pattern function calls with fresh
-- variables and accumulate new conditions.
expandRule :: IORef Int -> Set.Set Name -> Rule -> FreshM (Rule, Bool)
expandRule ref pfNames (Fact (RAtom (Atom p ts))) = do
  (ts', newConds, changed) <- expandTerms ref pfNames 0 ts
  if changed
    then return (Rule newConds (RAtom (Atom p ts')), True)
    else return (Fact (RAtom (Atom p ts')), False)
expandRule ref pfNames (Rule cs r) = do
  (r', rConds, rChanged) <- expandResult ref pfNames r
  (cs', cConds, cChanged) <- expandConds ref pfNames cs
  let allNewConds = rConds ++ cConds
  if rChanged || cChanged
    then return (Rule (cs' ++ allNewConds) r', True)
    else return (Rule cs' r', False)
expandRule _ _ rule = return (rule, False)

-- Expand pattern function calls in a Result
expandResult :: IORef Int -> Set.Set Name -> Result -> FreshM (Result, [Cond], Bool)
expandResult ref pfNames (RAtom (Atom p ts)) = do
  (ts', conds, changed) <- expandTerms ref pfNames 0 ts
  return (RAtom (Atom p ts'), conds, changed)
expandResult _ _ r = return (r, [], False)

-- Expand pattern function calls in a list of conditions
expandConds :: IORef Int -> Set.Set Name -> [Cond] -> FreshM ([Cond], [Cond], Bool)
expandConds ref pfNames cs = do
  results <- mapM (expandCond ref pfNames 0) cs
  let (cs', condLists, changes) = unzip3 results
  return (cs', concat condLists, or changes)

-- Expand pattern function calls in a single condition, tracking TPrev depth
expandCond :: IORef Int -> Set.Set Name -> Int -> Cond -> FreshM (Cond, [Cond], Bool)
expandCond ref pfNames depth (CAtom (Atom p ts)) = do
  (ts', conds, changed) <- expandTerms ref pfNames depth ts
  return (CAtom (Atom p ts'), conds, changed)
expandCond ref pfNames depth (CPrev c) = do
  (c', conds, changed) <- expandCond ref pfNames (depth + 1) c
  return (CPrev c', conds, changed)
expandCond ref pfNames depth (CNeg c) = do
  (c', conds, changed) <- expandCond ref pfNames depth c
  return (CNeg c', conds, changed)
expandCond ref pfNames depth (CAnd cs) = do
  results <- mapM (expandCond ref pfNames depth) cs
  let (cs', condLists, changes) = unzip3 results
  return (CAnd cs', concat condLists, or changes)
expandCond _ _ _ c = return (c, [], False)

-- Expand pattern function calls in a list of terms. The depth parameter
-- tracks how many TPrev wrappers we are inside, so new conditions get
-- wrapped in the appropriate number of CPrev.
expandTerms :: IORef Int -> Set.Set Name -> Int -> [Term] -> FreshM ([Term], [Cond], Bool)
expandTerms ref pfNames depth ts = do
  results <- mapM (expandTerm ref pfNames depth) ts
  let (ts', condLists, changes) = unzip3 results
  return (ts', concat condLists, or changes)

-- Expand a single term. If it's a pattern function call TFun f args where f
-- is a known pattern function, replace with a fresh variable and emit a
-- new condition. Otherwise recurse into subterms.
expandTerm :: IORef Int -> Set.Set Name -> Int -> Term -> FreshM (Term, [Cond], Bool)
expandTerm ref pfNames depth (TFun f args)
  | Set.member f pfNames = do
      -- This is a pattern function call: replace with fresh var, add condition.
      -- We don't recurse into args here; the fixpoint iteration will handle
      -- any nested pattern function calls in subsequent passes.
      v <- freshName ref "V"
      let freshVar = TVar v
          newCond = nestCPrev depth (CAtom (Atom f (args ++ [freshVar])))
      return (freshVar, [newCond], True)
  | otherwise = do
      -- Not a pattern function, but recurse into subterms
      (args', conds, changed) <- expandTerms ref pfNames depth args
      return (TFun f args', conds, changed)
expandTerm ref pfNames depth (TPrev t) = do
  (t', conds, changed) <- expandTerm ref pfNames (depth + 1) t
  return (TPrev t', conds, changed)
expandTerm _ _ _ t@(TVar _) = return (t, [], False)

-- ============================================================
-- Step 4: Push negation to atomic level
-- After this step, every negation is directly on an atomic formula.
-- ============================================================

-- | Step 4: Push negation to atomic level (paper p. 13)
step4 :: IORef Int -> [Rule] -> FreshM [Rule]
step4 ref = go maxNormalizerIterations
  where
    go 0 _ = fail "Normalizer step 4 (push negation to atoms) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM (step4Rule ref) rules
      let rs' = concat rs
      if any needsStep4 rs'
        then go (fuel - 1) rs'
        else return rs'

needsStep4 :: Rule -> Bool
needsStep4 (Fact _) = False
needsStep4 (Rule cs _) = any needsStep4Cond cs

needsStep4Cond :: Cond -> Bool
needsStep4Cond (CNeg c)  = not (isAtomOrPrevAtom c)
needsStep4Cond (CPrev c) = needsStep4Cond c
needsStep4Cond (CAnd cs) = any needsStep4Cond cs
needsStep4Cond _         = False

isAtomOrPrevAtom :: Cond -> Bool
isAtomOrPrevAtom (CAtom _) = True
isAtomOrPrevAtom (CPrev c) = isAtomOrPrevAtom c
isAtomOrPrevAtom _         = False

step4Rule :: IORef Int -> Rule -> FreshM [Rule]
step4Rule ref (Rule cs r) = do
  results <- mapM (step4Cond ref r) cs
  let (newConds, extraRules) = unzip results
  return (Rule newConds r : concat extraRules)
step4Rule _ rule = return [rule]

step4Cond :: IORef Int -> Result -> Cond -> FreshM (Cond, [Rule])
step4Cond ref _r (CNeg inner) | not (isAtomOrPrevAtom inner) = do
  -- ~a => r  ->  ~p(Xs) => r, a => p(Xs)
  -- where a is not just @^n(atom)
  let vs = Set.toList (fvCond inner)
      vterms = varsToTerms vs
  p <- freshName ref "neg"
  let pAtom = Atom p vterms
  return (CNeg (CAtom pAtom), [Rule [inner] (RAtom pAtom)])
step4Cond ref _r (CPrev c) = do
  (c', extras) <- step4Cond ref _r c
  return (CPrev c', extras)
step4Cond _ _ c = return (c, [])


-- ============================================================
-- Step 5: Distribute @ over /\ so each condition is @^m(~?)atom
-- ============================================================

-- | Step 5: Distribute @ over /\\ (paper p. 14)
step5 :: [Rule] -> [Rule]
step5 = map step5Rule

step5Rule :: Rule -> Rule
step5Rule (Rule cs r) = Rule (concatMap distributeAt cs) r
step5Rule rule = rule

-- Distribute @ over conjunction, and commute ~ and @ so @ is outermost
distributeAt :: Cond -> [Cond]
distributeAt (CPrev (CAnd cs)) = concatMap (distributeAt . CPrev) cs
distributeAt (CPrev c) =
  let cs = distributeAt c
  in map addPrev cs
-- Commute ~@ to @~  (valid under CWA)
distributeAt (CNeg (CPrev c)) = distributeAt (CPrev (CNeg c))
distributeAt (CAnd cs) = concatMap distributeAt cs
distributeAt c = [c]

addPrev :: Cond -> Cond
addPrev (CAtom a)        = CPrev (CAtom a)
addPrev (CNeg (CAtom a)) = CPrev (CNeg (CAtom a))
addPrev (CPrev c)        = CPrev (addPrev c)
addPrev c                = CPrev c

-- ============================================================
-- Convert to NormalRule after all steps
-- ============================================================

toNormalRule :: Rule -> Maybe NormalRule
toNormalRule (Fact (RAtom a)) = Just (NormalRule [] a)
toNormalRule (Rule cs (RAtom a)) = do
  ncs <- mapM toNormalCond cs
  return (NormalRule ncs a)
toNormalRule _ = Nothing  -- Should not happen after normalization

toNormalCond :: Cond -> Maybe NormalCond
toNormalCond = go 0 False
  where
    go depth neg (CPrev c)       = go (depth + 1) neg c
    go depth _   (CNeg (CAtom a)) = Just (NormalCond depth True a)
    go depth neg (CAtom a)       = Just (NormalCond depth neg a)
    go _ _ _                     = Nothing

-- ============================================================
-- Full normalization pipeline
-- ============================================================

-- | Full normalization pipeline: steps 1–5 then conversion to 'NormalRule'
normalize :: Program -> IO NormalProgram
normalize (Program rules pfs) = do
  ref <- newIORef 0
  -- Step 1: eliminate always, until, atnext (+ split conjunctions)
  r1 <- step1 ref rules
  -- Step 2: eliminate since, after, for, has-been, once
  r2 <- step2 ref r1
  -- Step 2.5: eliminate term-level TPrev (monadic: handles mixed depths)
  r2' <- eliminateTermPrevM ref r2
  -- Step 3: expand pattern functions
  r3 <- step3 ref pfs r2'
  -- Step 4: push negation to atoms
  r4 <- step4 ref r3
  -- Step 5: distribute @ over /\
  let r5 = step5 r4
  -- Convert to normal form
  let normals = map toNormalRule r5
  case sequence normals of
    Just ns -> do
      validateSafety ns
      return ns
    Nothing -> fail $ "Normalization produced non-normal rules:\n" ++
                      unlines [show r | r <- r5]

-- | Validate that every variable in a negated condition (at depth 0)
-- is bound by at least one positive condition in the same rule.
validateSafety :: NormalProgram -> IO ()
validateSafety = mapM_ checkRule
  where
    checkRule rule = do
      let posVars = Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, not (ncNegated c)]
          negVars = Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, ncNegated c, ncPrevDepth c == 0]
          unsafeVars = negVars `Set.difference` posVars
      unless (Set.null unsafeVars) $
        hPutStrLn stderr $ "Warning: variable(s) " ++ show (Set.toList unsafeVars) ++
                          " appear in negated condition(s) but are not bound by any positive condition.\n" ++
                          "  Rule: " ++ ppNormalRule rule ++ "\n" ++
                          "  Hint: bind variables in positive conditions first, e.g.:\n" ++
                          "    r(X) /\\ ~p(X) => q(X).    -- X is bound by r(X) before ~p(X)"
