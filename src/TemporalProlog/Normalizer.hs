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
--    converts @f(args) -> body@ definitions to predicate clauses; second
--    substep replaces nested function calls in terms with fresh variables
--    and auxiliary conditions (including within PF clauses themselves,
--    so recursive PF calls become conditions for backward chaining).
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
  , FreshNameGen(..)
  , FreshM
  , step1
  , step2
  , eliminateTermPrevM
  , step3
  , step4
  , step5
  ) where

import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Set as Set
import TemporalProlog.PrettyPrint (ppNormalRule)
import TemporalProlog.Syntax

-- | Counter for generating fresh auxiliary names.
newtype FreshNameGen = FreshNameGen Int

-- | Fresh name generation monad with error reporting.
type FreshM = ExceptT String (State FreshNameGen)

freshName :: String -> FreshM Name
freshName prefix = do
  FreshNameGen n <- get
  put (FreshNameGen (n + 1))
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
step1 :: [Rule] -> FreshM [Rule]
step1 = go maxNormalizerIterations
  where
    go 0 _ = throwError "Normalizer step 1 (eliminate always/until/atnext) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM step1Rule rules
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

step1Rule :: Rule -> FreshM [Rule]
step1Rule rule = case rule of
  Fact (RAnd rs) -> return [Fact r | r <- flattenResults (RAnd rs)]
  Rule cs (RAnd rs) ->
    return [Rule cs r | r <- flattenResults (RAnd rs)]
  Rule cs r | any isCAnd cs -> do
    let cs' = concatMap flattenConds cs
    step1Rule (Rule cs' r)
    where isCAnd (CAnd _) = True
          isCAnd _ = False
  Fact (RAlways q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName "always"
    let pAtom = Atom p vterms
    return [ Fact q
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           , Rule [CAtom pAtom] q
           ]
  Rule cs (RAlways q) -> do
    let vs = Set.toList $ Set.union (Set.unions (map fvCond cs)) (fvResult q)
        vterms = varsToTerms vs
    p <- freshName "always"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           , Rule [CAtom pAtom] q
           ]
  Fact (RUntil q a) ->
    -- Unconditional "q until a" means q holds whenever a is false.
    -- This is consistent with the paper's treatment of bare facts as
    -- universally valid: q resumes if a becomes false again.
    return [ Rule [CNeg a] q ]
  Rule cs (RUntil q b) -> do
    let vs = Set.toList $ Set.union (fvResult q) (fvCond b)
        vterms = varsToTerms vs
    p <- freshName "until"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CNeg b] (RAtom pAtom)
           , Rule [CAtom pAtom, CNeg b] q
           ]
  Fact (RAtNext q b) -> do
    let vs = Set.toList $ Set.union (fvResult q) (fvCond b)
        vterms = varsToTerms vs
    p <- freshName "atnext"
    let pAtom = Atom p vterms
    return [ Fact (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CPrev (CNeg b)] (RAtom pAtom)
           , Rule [CAtom pAtom, b] q
           ]
  Rule cs (RAtNext q b) -> do
    let vs = Set.toList $ Set.union (fvResult q) (fvCond b)
        vterms = varsToTerms vs
    p <- freshName "atnext"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), CPrev (CNeg b)] (RAtom pAtom)
           , Rule [CAtom pAtom, b] q
           ]
  Fact (RNext q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName "next"
    let pAtom = Atom p vterms
    return [ Fact (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] q
           ]
  Rule cs (RNext q) -> do
    let vs = resultVars q
        vterms = varsToTerms vs
    p <- freshName "next"
    let pAtom = Atom p vterms
    return [ Rule cs (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] q
           ]
  _ -> return [rule]

-- ============================================================
-- Step 2: Eliminate since, after, for, has-been (#), once (?)
-- ============================================================

-- | Step 2: Eliminate since, after, for, ■, ◆ (paper pp. 10–11)
step2 :: [Rule] -> FreshM [Rule]
step2 = go maxNormalizerIterations
  where
    go 0 _ = throwError "Normalizer step 2 (eliminate since/after/for/has-been/once) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM step2Rule rules
      let rs' = concat rs
      if any needsStep2 rs'
        then go (fuel - 1) rs'
        else return rs'

needsStep2 :: Rule -> Bool
needsStep2 (Fact _) = False
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

step2Rule :: Rule -> FreshM [Rule]
step2Rule rule@(Rule cs r) = case findStep2 cs of
  Nothing -> return [rule]
  Just (before, op, after_) -> transformStep2 op r (before ++ after_)
step2Rule rule = return [rule]

findStep2 :: [Cond] -> Maybe ([Cond], Cond, [Cond])
findStep2 = go []
  where
    go _ [] = Nothing
    go acc (c:cs)
      | hasStep2Op c = Just (reverse acc, c, cs)
      | otherwise    = go (c:acc) cs

transformStep2 :: Cond -> Result -> [Cond] -> FreshM [Rule]
transformStep2 cond r otherConds = case cond of
  CHasBeen a -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "hasbeen"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a, CAtom (Atom "at" [TFun "0" []])] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]
  COnce a -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "once"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           ]
  CSince a b -> do
    let allVars = Set.toList $ Set.unions
          [fvCond a, fvCond b, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "since"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [b, a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]
  CAfter a b -> do
    -- "a after b" means: b held at some past time, and a holds at some point
    -- after b. The auxiliary tracks that b has occurred; a is checked directly.
    let allVars = Set.toList $ Set.unions
          [fvCond a, fvCond b, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "after"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : a : otherConds) r
           , Rule [b] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           ]
  CEventually a -> transformStep2 (COnce a) r otherConds
  CFor a n -> do
    let expanded = [nestPrev i a | i <- [0..n-1]]
    return [Rule (expanded ++ otherConds) r]
  CNeg inner | hasStep2Op inner -> do
    let allVars = Set.toList $ Set.unions
          [fvCond inner, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "neg"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    innerRules <- transformStep2 inner (RAtom pAtom) []
    return $ Rule (CNeg pCond : otherConds) r : innerRules
  CPrev inner | hasStep2Op inner -> do
    let allVars = Set.toList $ Set.unions
          [fvCond inner, Set.unions (map fvCond otherConds), fvResult r]
        vterms = varsToTerms allVars
    p <- freshName "prev"
    let pAtom = Atom p vterms
        pCond = CPrev (CAtom pAtom)
    innerRules <- transformStep2 inner (RAtom pAtom) []
    return $ Rule (pCond : otherConds) r : innerRules
  _ -> return [Rule (cond : otherConds) r]

nestPrev :: Int -> Cond -> Cond
nestPrev 0 c = c
nestPrev n c = CPrev (nestPrev (n-1) c)

-- ============================================================
-- Eliminate term-level TPrev by converting to condition-level CPrev
-- ============================================================

-- | Handles mixed TPrev depths via auxiliary predicates.
eliminateTermPrevM :: [Rule] -> FreshM [Rule]
eliminateTermPrevM rules = do
  results <- mapM eliminateTermPrevRuleM rules
  return (concat results)

eliminateTermPrevRuleM :: Rule -> FreshM [Rule]
eliminateTermPrevRuleM (Fact (RAtom a)) =
  case maxTermPrevInAtom a of
    0 -> return [Fact (RAtom a)]
    _ -> throwError $ "TPrev in head atom not allowed: " ++ show a
eliminateTermPrevRuleM (Fact r) = return [Fact r]
eliminateTermPrevRuleM (Rule conds result) =
  case result of
    RAtom a | maxTermPrevInAtom a > 0 ->
      throwError $ "TPrev in head atom not allowed: " ++ show a
    _ -> do
      results <- mapM liftTermPrevM conds
      let (conds', ruleLists) = unzip results
      return (Rule conds' result : concat ruleLists)

liftTermPrevM :: Cond -> FreshM (Cond, [Rule])
liftTermPrevM (CAtom (Atom name terms)) = do
  let depths = map termPrevDepth terms
      maxD = maximum (0 : depths)
  if maxD == 0
    then return (CAtom (Atom name terms), [])
    else if all (== maxD) depths
      then let terms' = map (stripTermPrevN maxD) terms
           in return (nestCPrev maxD (CAtom (Atom name terms')), [])
      else decomposeMixedDepths name terms depths
liftTermPrevM (CPrev c) = do
  (c', rules) <- liftTermPrevM c
  return (CPrev c', rules)
liftTermPrevM (CNeg c) = do
  (c', rules) <- liftTermPrevM c
  return (CNeg c', rules)
liftTermPrevM (CAnd cs) = do
  results <- mapM liftTermPrevM cs
  let (cs', ruleLists) = unzip results
  return (CAnd cs', concat ruleLists)
liftTermPrevM c = return (c, [])

decomposeMixedDepths :: Name -> [Term] -> [Int] -> FreshM (Cond, [Rule])
decomposeMixedDepths name terms depths = do
  let minD = minimum depths
      adjusted = map (\t -> stripTermPrevN minD t) terms
      adjustedDepths = map (\d -> d - minD) depths
  if all (== 0) adjustedDepths
    then return (nestCPrev minD (CAtom (Atom name adjusted)), [])
    else do
      let indexed = zip3 [0..] adjusted adjustedDepths
          nonZeroDs = Set.toList $ Set.fromList $ filter (> 0) adjustedDepths
      auxResults <- mapM (\d -> do
            let indicesAtD = [i | (i, _, dd) <- indexed, dd == d]
                strippedTerms = [stripTermPrevN d (adjusted !! i) | i <- indicesAtD]
            auxName <- freshName (name ++ "_d" ++ show d)
            let auxCond = nestCPrev d (CAtom (Atom auxName strippedTerms))
            let freshVars = [TVar ("_TP" ++ show i) | i <- [0..length terms - 1]]
                projArgs = [freshVars !! i | i <- indicesAtD]
                auxRule = Rule [CAtom (Atom name freshVars)] (RAtom (Atom auxName projArgs))
            return (auxCond, auxRule)
          ) nonZeroDs
      let baseTerms = [stripTermPrevN d t | (_, t, d) <- indexed]
          mainCond = CAtom (Atom name baseTerms)
          allConds = mainCond : map fst auxResults
          combined = CAnd allConds
          wrappedCond = nestCPrev minD combined
          allRules = map snd auxResults
      return (wrappedCond, allRules)

termPrevDepth :: Term -> Int
termPrevDepth (TPrev t) = 1 + termPrevDepth t
termPrevDepth _ = 0

maxTermPrevInAtom :: Atom -> Int
maxTermPrevInAtom (Atom _ terms) = maximum (0 : map maxTermPrevInTerm terms)

maxTermPrevInTerm :: Term -> Int
maxTermPrevInTerm (TPrev t) = 1 + maxTermPrevInTerm t
maxTermPrevInTerm (TFun _ ts) = maximum (0 : map maxTermPrevInTerm ts)
maxTermPrevInTerm _ = 0

stripTermPrevN :: Int -> Term -> Term
stripTermPrevN 0 t = t
stripTermPrevN n (TPrev t) = stripTermPrevN (n-1) t
stripTermPrevN _ t = t

nestCPrev :: Int -> Cond -> Cond
nestCPrev 0 c = c
nestCPrev n c = CPrev (nestCPrev (n-1) c)

-- ============================================================
-- Step 3: Expand pattern functions
-- ============================================================

step3 :: [PatternFunc] -> [Rule] -> FreshM [Rule]
step3 [] rules = return rules
step3 pfs rules = do
  let pfRules = map patternFuncToRule pfs
      pfNames = Set.fromList [n | PatternFunc n _ _ <- pfs]
  expandRulesFixpoint pfNames (pfRules ++ rules)

patternFuncToRule :: PatternFunc -> Rule
patternFuncToRule (PatternFunc f args body) =
  Fact (RAtom (Atom f (args ++ [body])))

expandRulesFixpoint :: Set.Set Name -> [Rule] -> FreshM [Rule]
expandRulesFixpoint pfNames rules = do
  results <- mapM (expandRule pfNames) rules
  let (rules', changed) = unzip results
  if or changed
    then expandRulesFixpoint pfNames rules'
    else return rules'

expandRule :: Set.Set Name -> Rule -> FreshM (Rule, Bool)
expandRule pfNames (Fact (RAtom (Atom p ts))) = do
  (ts', newConds, changed) <- expandTerms pfNames 0 ts
  if changed
    then return (Rule newConds (RAtom (Atom p ts')), True)
    else return (Fact (RAtom (Atom p ts')), False)
expandRule pfNames (Rule cs r) = do
  (r', rConds, rChanged) <- expandResult pfNames r
  (cs', cConds, cChanged) <- expandConds pfNames cs
  let allNewConds = rConds ++ cConds
  if rChanged || cChanged
    then return (Rule (cs' ++ allNewConds) r', True)
    else return (Rule cs' r', False)
expandRule _ rule = return (rule, False)

expandResult :: Set.Set Name -> Result -> FreshM (Result, [Cond], Bool)
expandResult pfNames (RAtom (Atom p ts)) = do
  (ts', conds, changed) <- expandTerms pfNames 0 ts
  return (RAtom (Atom p ts'), conds, changed)
expandResult _ r = return (r, [], False)

expandConds :: Set.Set Name -> [Cond] -> FreshM ([Cond], [Cond], Bool)
expandConds pfNames cs = do
  results <- mapM (expandCond pfNames 0) cs
  let (cs', condLists, changes) = unzip3 results
  return (cs', concat condLists, or changes)

expandCond :: Set.Set Name -> Int -> Cond -> FreshM (Cond, [Cond], Bool)
expandCond pfNames depth (CAtom (Atom p ts)) = do
  (ts', conds, changed) <- expandTerms pfNames depth ts
  return (CAtom (Atom p ts'), conds, changed)
expandCond pfNames depth (CPrev c) = do
  (c', conds, changed) <- expandCond pfNames (depth + 1) c
  return (CPrev c', conds, changed)
expandCond pfNames depth (CNeg c) = do
  (c', conds, changed) <- expandCond pfNames depth c
  return (CNeg c', conds, changed)
expandCond pfNames depth (CAnd cs) = do
  results <- mapM (expandCond pfNames depth) cs
  let (cs', condLists, changes) = unzip3 results
  return (CAnd cs', concat condLists, or changes)
expandCond _ _ c = return (c, [], False)

expandTerms :: Set.Set Name -> Int -> [Term] -> FreshM ([Term], [Cond], Bool)
expandTerms pfNames depth ts = do
  results <- mapM (expandTerm pfNames depth) ts
  let (ts', condLists, changes) = unzip3 results
  return (ts', concat condLists, or changes)

expandTerm :: Set.Set Name -> Int -> Term -> FreshM (Term, [Cond], Bool)
expandTerm pfNames depth (TFun f args)
  | Set.member f pfNames = do
      v <- freshName "V"
      let freshVar = TVar v
          newCond = nestCPrev depth (CAtom (Atom f (args ++ [freshVar])))
      return (freshVar, [newCond], True)
  | otherwise = do
      (args', conds, changed) <- expandTerms pfNames depth args
      return (TFun f args', conds, changed)
expandTerm pfNames depth (TPrev t) = do
  (t', conds, changed) <- expandTerm pfNames (depth + 1) t
  return (TPrev t', conds, changed)
expandTerm _ _ t@(TVar _) = return (t, [], False)

-- ============================================================
-- Step 4: Push negation to atomic level
-- ============================================================

step4 :: [Rule] -> FreshM [Rule]
step4 = go maxNormalizerIterations
  where
    go 0 _ = throwError "Normalizer step 4 (push negation to atoms) did not converge within iteration limit"
    go fuel rules = do
      rs <- mapM step4Rule rules
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

step4Rule :: Rule -> FreshM [Rule]
step4Rule (Rule cs r) = do
  results <- mapM step4Cond cs
  let (newConds, extraRules) = unzip results
  return (Rule newConds r : concat extraRules)
step4Rule rule = return [rule]

step4Cond :: Cond -> FreshM (Cond, [Rule])
step4Cond (CNeg inner) | not (isAtomOrPrevAtom inner) = do
  let vs = Set.toList (fvCond inner)
      vterms = varsToTerms vs
  p <- freshName "neg"
  let pAtom = Atom p vterms
  return (CNeg (CAtom pAtom), [Rule [inner] (RAtom pAtom)])
step4Cond (CPrev c) = do
  (c', extras) <- step4Cond c
  return (CPrev c', extras)
step4Cond c = return (c, [])

-- ============================================================
-- Step 5: Distribute @ over /\ so each condition is @^m(~?)atom
-- ============================================================

step5 :: [Rule] -> [Rule]
step5 = map step5Rule

step5Rule :: Rule -> Rule
step5Rule (Rule cs r) = Rule (concatMap distributeAt cs) r
step5Rule rule = rule

distributeAt :: Cond -> [Cond]
distributeAt (CPrev (CAnd cs)) = concatMap (distributeAt . CPrev) cs
distributeAt (CPrev c) =
  let cs = distributeAt c
  in map addPrev cs
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
toNormalRule _ = Nothing

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

-- | Full normalization pipeline: steps 1–5 then conversion to 'NormalRule'.
--   Returns @Left err@ for user-facing errors (invalid input, non-convergence)
--   or @Right ((program, pfNames), warnings)@ on success.
normalize :: Program -> Either String ((NormalProgram, Set.Set Name), [String])
normalize (Program rules pfs) =
  let pfNames = Set.fromList [n | PatternFunc n _ _ <- pfs]
      (result, _) = runState (runExceptT pipeline) (FreshNameGen 0)
      pipeline = do
        r1 <- step1 rules
        r2 <- step2 r1
        r2' <- eliminateTermPrevM r2
        r3 <- step3 pfs r2'
        r4 <- step4 r3
        let r5 = step5 r4
        let normals = map toNormalRule r5
        case sequence normals of
          Just ns ->
            let warnings = validateSafety ns
            in return ((ns, pfNames), warnings)
          Nothing -> throwError $ "Normalization produced non-normal rules:\n" ++
                                  unlines [show r | r <- r5]
  in result

-- | Validate that every variable in a negated condition (at depth 0)
-- is bound by at least one positive condition in the same rule.
validateSafety :: NormalProgram -> [String]
validateSafety = concatMap checkRule
  where
    checkRule rule =
      let posVars = Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, not (ncNegated c)]
          negVars = Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, ncNegated c, ncPrevDepth c == 0]
          unsafeVars = negVars `Set.difference` posVars
      in if Set.null unsafeVars
         then []
         else ["Warning: variable(s) " ++ show (Set.toList unsafeVars) ++
               " appear in negated condition(s) but are not bound by any positive condition.\n" ++
               "  Rule: " ++ ppNormalRule rule ++ "\n" ++
               "  Hint: bind variables in positive conditions first, e.g.:\n" ++
               "    r(X) /\\ ~p(X) => q(X).    -- X is bound by r(X) before ~p(X)"]
