module TemporalProlog.Normalizer
  ( normalize
  , step1
  , step2
  , step3
  , step4
  , step5
  ) where

import Control.Monad (unless)
import Data.IORef
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

  -- Base case: no transformation needed
  _ -> return [rule]

-- ============================================================
-- Step 2: Eliminate since, after, for, has-been (#), once (?)
-- ============================================================

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
-- Step 3: Expand pattern functions
-- (Simplified: we convert pattern func defs into predicate rules)
-- ============================================================

step3 :: [PatternFunc] -> [Rule] -> [Rule]
step3 [] rules = rules
step3 pfs rules =
  -- First substep: convert f(t1,...,tk) -> t0 into f(t1,...,tk,t0) predicate
  let pfRules = map patternFuncToRule pfs
      -- Second substep: expand function calls in terms within rules
      rules' = map (expandFuncCallsInRule pfs) rules
  in pfRules ++ rules'

patternFuncToRule :: PatternFunc -> Rule
patternFuncToRule (PatternFunc f args body) =
  Fact (RAtom (Atom f (args ++ [body])))

-- Replace occurrences of pattern function calls f(t1,...,tk) in terms
-- with a fresh variable X, and add condition f(t1,...,tk,X) to the rule
expandFuncCallsInRule :: [PatternFunc] -> Rule -> Rule
expandFuncCallsInRule pfs rule =
  let pfNames = [n | PatternFunc n _ _ <- pfs]
  in expandRule pfNames rule

expandRule :: [Name] -> Rule -> Rule
expandRule _ rule = rule  -- For now, pass through. Full expansion would require
                          -- detecting function applications in term position.
                          -- The simple case (explicit -> definitions) is handled
                          -- by converting to predicate facts above.

-- ============================================================
-- Step 4: Push negation to atomic level
-- After this step, every negation is directly on an atomic formula.
-- ============================================================

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

normalize :: Program -> IO NormalProgram
normalize (Program rules pfs) = do
  ref <- newIORef 0
  -- Step 1: eliminate always, until, atnext (+ split conjunctions)
  r1 <- step1 ref rules
  -- Step 2: eliminate since, after, for, has-been, once
  r2 <- step2 ref r1
  -- Step 3: expand pattern functions
  let r3 = step3 pfs r2
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
        hPutStrLn stderr $ "Warning: unsafe rule - variables " ++ show (Set.toList unsafeVars) ++
                          " in negated conditions not bound by positive conditions: " ++
                          ppNormalRule rule
