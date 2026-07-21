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
--    @~@ directly precedes an atom. Negation outside a previous-time formula
--    is preserved with an auxiliary predicate.
--
-- 5. __Step 5__ (p. 14): Distribute @\@@ over @/\\@ so each condition has
--    the canonical form @@^m(~?)atom@.
--
-- Each step iterates until a termination condition is met (the relevant
-- operator class is absent). The paper proves termination because each
-- step strictly decreases the count of its target operators.
module TemporalProlog.Normalizer
  ( normalize
  , normalizeDetailed
  , validateProgramSymbols
  , NormalizationResult(..)
  , FreshNameGen(..)
  , FreshM
  , maxForRepetitions
  , step1
  , step2
  , eliminateTermPrevM
  , step3
  , step4
  , step5
  ) where

import Control.Monad (foldM)
import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import TemporalProlog.PrettyPrint (ppNormalRule)
import TemporalProlog.Syntax

-- | Counter for generating auxiliary predicate and variable names. The full
-- normalizer seeds it above every source identifier ending in @_auxN@, which
-- keeps generated identifiers fresh while preserving the public constructor.
newtype FreshNameGen = FreshNameGen Integer

-- | Fresh name generation monad with error reporting.
type FreshM = ExceptT String (State FreshNameGen)

-- | Normalized executable program together with the metadata required by
-- user-facing tools to distinguish source predicates from generated ones.
data NormalizationResult = NormalizationResult
  { normalizedProgram             :: NormalProgram
  , normalizedPatternFunctions    :: Set.Set Name
  , normalizedAuxiliaryPredicates :: Set.Set Name
  , normalizationWarnings         :: [String]
  } deriving (Eq, Show)

-- ============================================================
-- Source symbol-signature validation
-- ============================================================

data AtomRole = ConditionAtom | ResultAtom
  deriving (Eq, Show)

data SignatureState = SignatureState
  { signaturePatternFunctions :: Map.Map Name Int
  , signaturePredicates       :: Map.Map Name Int
  , signatureConstructors     :: Map.Map Name Int
  }

type SignatureM = StateT SignatureState (Either String)

-- | Validate the source-level fixed-signature and namespace contract before
-- normalization can erase distinctions or silently discard malformed rules.
validateProgramSymbols :: Program -> Either String ()
validateProgramSymbols program@(Program rules patternFunctions) = do
  patternSignatures <- foldM addPatternSignature Map.empty
    (patternDeclarations program)
  let initial = SignatureState patternSignatures Map.empty Map.empty
  evalStateT
    (mapM_ validatePatternFunction patternFunctions
      >> mapM_ validateSourceRule rules)
    initial

patternDeclarations :: Program -> [(Name, Int)]
patternDeclarations (Program rules patternFunctions) =
  [ (name, length args)
  | PatternFunc name args _ <- patternFunctions
  ] ++ concatMap rulePatternDeclarations rules

rulePatternDeclarations :: Rule -> [(Name, Int)]
rulePatternDeclarations (Fact result) = resultPatternDeclarations result
rulePatternDeclarations (Rule _ result) = resultPatternDeclarations result

resultPatternDeclarations :: Result -> [(Name, Int)]
resultPatternDeclarations (RAtom _) = []
resultPatternDeclarations (RPatternFunc name args _) = [(name, length args)]
resultPatternDeclarations (RAlways result) = resultPatternDeclarations result
resultPatternDeclarations (RUntil result _) = resultPatternDeclarations result
resultPatternDeclarations (RAtNext result _) = resultPatternDeclarations result
resultPatternDeclarations (RAnd results) = concatMap resultPatternDeclarations results
resultPatternDeclarations (RNext result) = resultPatternDeclarations result

addPatternSignature
  :: Map.Map Name Int
  -> (Name, Int)
  -> Either String (Map.Map Name Int)
addPatternSignature signatures (name, arity)
  | externalPredicateArity name /= Nothing
      || arithmeticFunctionArity name /= Nothing =
      Left $ "Pattern function name '" ++ name ++ "' is reserved"
  | otherwise = case Map.lookup name signatures of
      Nothing -> Right (Map.insert name arity signatures)
      Just expected
        | expected == arity -> Right signatures
        | otherwise -> Left $
            "Pattern function '" ++ name
            ++ "' has inconsistent input arity: expected " ++ show expected
            ++ ", found " ++ show arity

validatePatternFunction :: PatternFunc -> SignatureM ()
validatePatternFunction (PatternFunc _ args body) =
  mapM_ validateSourceTerm (body : args)

validateSourceRule :: Rule -> SignatureM ()
validateSourceRule (Fact result) = validateSourceResult result
validateSourceRule (Rule conditions result) =
  mapM_ validateSourceCond conditions >> validateSourceResult result

validateSourceResult :: Result -> SignatureM ()
validateSourceResult (RAtom atom) = validateSourceAtom ResultAtom atom
validateSourceResult (RPatternFunc _ args body) =
  mapM_ validateSourceTerm (body : args)
validateSourceResult (RAlways result) = validateSourceResult result
validateSourceResult (RUntil result condition) =
  validateSourceResult result >> validateSourceCond condition
validateSourceResult (RAtNext result condition) =
  validateSourceResult result >> validateSourceCond condition
validateSourceResult (RAnd results) = mapM_ validateSourceResult results
validateSourceResult (RNext result) = validateSourceResult result

validateSourceCond :: Cond -> SignatureM ()
validateSourceCond (CAtom atom) = validateSourceAtom ConditionAtom atom
validateSourceCond (CNeg condition) = validateSourceCond condition
validateSourceCond (CPrev condition) = validateSourceCond condition
validateSourceCond (CHasBeen condition) = validateSourceCond condition
validateSourceCond (COnce condition) = validateSourceCond condition
validateSourceCond (CSince left right) =
  validateSourceCond left >> validateSourceCond right
validateSourceCond (CAfter left right) =
  validateSourceCond left >> validateSourceCond right
validateSourceCond (CFor condition _) = validateSourceCond condition
validateSourceCond (CAnd conditions) = mapM_ validateSourceCond conditions
validateSourceCond (CEventually condition) = validateSourceCond condition

validateSourceAtom :: AtomRole -> Atom -> SignatureM ()
validateSourceAtom role (Atom name terms) = do
  patterns <- gets signaturePatternFunctions
  case externalPredicateArity name of
    Just expected
      | role == ResultAtom -> validationError $
          "External predicate '" ++ name ++ "' cannot appear in a rule result"
      | expected /= length terms -> validationError $
          "External predicate '" ++ name ++ "' expects arity "
          ++ show expected ++ ", found " ++ show (length terms)
      | otherwise -> return ()
    Nothing -> case Map.lookup name patterns of
      Just inputArity
        | length terms /= inputArity + 1 -> validationError $
            "Pattern function '" ++ name ++ "' has relational arity "
            ++ show (inputArity + 1) ++ ", found " ++ show (length terms)
        | otherwise -> return ()
      Nothing -> rememberPredicate name (length terms)
  mapM_ validateSourceTerm terms

validateSourceTerm :: Term -> SignatureM ()
validateSourceTerm (TVar _) = return ()
validateSourceTerm (TPrev term) = validateSourceTerm term
validateSourceTerm (TFun name terms) = do
  patterns <- gets signaturePatternFunctions
  case Map.lookup name patterns of
    Just expected
      | expected /= length terms -> validationError $
          "Pattern function '" ++ name ++ "' expects input arity "
          ++ show expected ++ ", found " ++ show (length terms)
      | otherwise -> return ()
    Nothing -> case arithmeticFunctionArity name of
      Just expected
        | expected /= length terms -> validationError $
            "Arithmetic operator '" ++ name ++ "' expects arity "
            ++ show expected ++ ", found " ++ show (length terms)
        | otherwise -> return ()
      Nothing -> rememberConstructor name (length terms)
  mapM_ validateSourceTerm terms

rememberPredicate :: Name -> Int -> SignatureM ()
rememberPredicate name arity = do
  signatures <- gets signaturePredicates
  case Map.lookup name signatures of
    Nothing -> modify' $ \signatureState -> signatureState
      { signaturePredicates = Map.insert name arity signatures }
    Just expected
      | expected == arity -> return ()
      | otherwise -> validationError $
          "Predicate '" ++ name ++ "' has inconsistent arity: expected "
          ++ show expected ++ ", found " ++ show arity

rememberConstructor :: Name -> Int -> SignatureM ()
rememberConstructor name arity = do
  signatures <- gets signatureConstructors
  case Map.lookup name signatures of
    Nothing -> modify' $ \signatureState -> signatureState
      { signatureConstructors = Map.insert name arity signatures }
    Just expected
      | expected == arity -> return ()
      | otherwise -> validationError $
          "Constructor '" ++ name ++ "' has inconsistent arity: expected "
          ++ show expected ++ ", found " ++ show arity

validationError :: String -> SignatureM a
validationError = lift . Left

freshName :: String -> FreshM Name
freshName prefix = do
  FreshNameGen n <- get
  put (FreshNameGen (n + 1))
  return (prefix ++ "_aux" ++ show n)

-- | Maximum iterations for normalizer fixed-point loops
maxNormalizerIterations :: Int
maxNormalizerIterations = 1000

-- | Largest @for@ count admitted by the portable executable profile.  The
-- source AST retains arbitrary-precision counts; this bound is checked before
-- expansion so an oversized count cannot wrap or exhaust normalization.
maxForRepetitions :: Integer
maxForRepetitions = 1000

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
  -- Paper step 1(2): an unconditional []q is simply q.  A bare result
  -- formula is required to hold at every world, so no persistence predicate
  -- is needed here.
  Fact (RAlways q) -> return [Fact q]
  Rule cs (RAlways q) -> do
    -- The paper puts exactly fv(q) in the auxiliary predicate.  Capturing
    -- variables that occur only in the antecedent can make the recurrence
    -- non-ground and silently disable an otherwise valid rule.
    let vs = resultVars q
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
           , Rule [CPrev (CAtom pAtom), CPrev (CNeg b)] (RAtom pAtom)
           , Rule [CAtom pAtom, CNeg b] q
           ]
  -- Paper step 1(4): without an antecedent, q atnext b is b => q.
  Fact (RAtNext q b) -> return [Rule [b] q]
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
  -- Step 2 transformations can expose a conjunction that was nested inside
  -- another temporal operator.  Step 1 has already run, so flatten it here
  -- to expose any remaining operators instead of spinning to the fuel limit.
  CAnd cs -> return [Rule (concatMap flattenConds cs ++ otherConds) r]
  CHasBeen a -> do
    let allVars = Set.toList (fvCond a)
        vterms = varsToTerms allVars
    p <- freshName "hasbeen"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a, CAtom (Atom "at" [TFun "0" []])] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]
  COnce a -> do
    let allVars = Set.toList (fvCond a)
        vterms = varsToTerms allVars
    p <- freshName "once"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           ]
  CSince a b -> do
    let allVars = Set.toList (Set.union (fvCond a) (fvCond b))
        vterms = varsToTerms allVars
    p <- freshName "since"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [b, a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom), a] (RAtom pAtom)
           ]
  CAfter a b -> do
    -- The prose definition in paper section 3 is strict: b must be
    -- witnessed in an earlier world and a in a later one.  Printed step
    -- 2(4) instead implements "a is more recent than b"; that recurrence
    -- is an erratum.  Use one persistent latch for b and a second persistent
    -- latch for the completed strict witness.
    let bVars = Set.toList (fvCond b)
        allVars = Set.toList (Set.union (fvCond a) (fvCond b))
        bTerms = varsToTerms bVars
        allTerms = varsToTerms allVars
    seen <- freshName "after_seen"
    p <- freshName "after"
    let seenAtom = Atom seen bTerms
        pAtom = Atom p allTerms
        pCond = CAtom pAtom
    return [ Rule (pCond : otherConds) r
           , Rule [b] (RAtom seenAtom)
           , Rule [CPrev (CAtom seenAtom)] (RAtom seenAtom)
           , Rule [CPrev (CAtom seenAtom), a] (RAtom pAtom)
           , Rule [CPrev (CAtom pAtom)] (RAtom pAtom)
           ]
  CEventually a -> transformStep2 (COnce a) r otherConds
  CFor a n -> do
    if n <= 0
      then throwError "The right operand of 'for' must be a positive integer"
      else if n > maxForRepetitions
        then throwError $ "The right operand of 'for' exceeds the executable limit of "
          ++ show maxForRepetitions ++ " repetitions"
      else do
        let expanded = [nestPrev i a | i <- [0..fromInteger n - 1]]
        return [Rule (expanded ++ otherConds) r]
  CNeg inner | hasStep2Op inner -> do
    let allVars = Set.toList (fvCond inner)
        vterms = varsToTerms allVars
    p <- freshName "neg"
    let pAtom = Atom p vterms
        pCond = CAtom pAtom
    innerRules <- transformStep2 inner (RAtom pAtom) []
    return $ Rule (CNeg pCond : otherConds) r : innerRules
  CPrev inner | hasStep2Op inner -> do
    let allVars = Set.toList (fvCond inner)
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
-- Eliminate term-level TPrev after pattern-function expansion
-- ============================================================

-- | Paper step 3 first turns every pattern-function occurrence below a
-- term-level @ into a predicate condition with the corresponding condition
-- depth.  Once those conditions have been emitted, all @ operators still
-- attached to terms are erased (paper p. 316).
eliminateTermPrevM :: [Rule] -> FreshM [Rule]
eliminateTermPrevM = return . map stripRuleTermPrev

stripRuleTermPrev :: Rule -> Rule
stripRuleTermPrev (Fact r) = Fact (stripResultTermPrev r)
stripRuleTermPrev (Rule cs r) =
  Rule (map stripCondTermPrev cs) (stripResultTermPrev r)

stripResultTermPrev :: Result -> Result
stripResultTermPrev (RAtom a) = RAtom (stripAtomTermPrev a)
stripResultTermPrev (RPatternFunc f args body) =
  RPatternFunc f (map stripTermPrev args) (stripTermPrev body)
stripResultTermPrev (RAlways r) = RAlways (stripResultTermPrev r)
stripResultTermPrev (RUntil r c) =
  RUntil (stripResultTermPrev r) (stripCondTermPrev c)
stripResultTermPrev (RAtNext r c) =
  RAtNext (stripResultTermPrev r) (stripCondTermPrev c)
stripResultTermPrev (RAnd rs) = RAnd (map stripResultTermPrev rs)
stripResultTermPrev (RNext r) = RNext (stripResultTermPrev r)

stripCondTermPrev :: Cond -> Cond
stripCondTermPrev (CAtom a) = CAtom (stripAtomTermPrev a)
stripCondTermPrev (CNeg c) = CNeg (stripCondTermPrev c)
stripCondTermPrev (CPrev c) = CPrev (stripCondTermPrev c)
stripCondTermPrev (CHasBeen c) = CHasBeen (stripCondTermPrev c)
stripCondTermPrev (COnce c) = COnce (stripCondTermPrev c)
stripCondTermPrev (CSince c d) =
  CSince (stripCondTermPrev c) (stripCondTermPrev d)
stripCondTermPrev (CAfter c d) =
  CAfter (stripCondTermPrev c) (stripCondTermPrev d)
stripCondTermPrev (CFor c n) = CFor (stripCondTermPrev c) n
stripCondTermPrev (CAnd cs) = CAnd (map stripCondTermPrev cs)
stripCondTermPrev (CEventually c) = CEventually (stripCondTermPrev c)

stripAtomTermPrev :: Atom -> Atom
stripAtomTermPrev (Atom p ts) = Atom p (map stripTermPrev ts)

stripTermPrev :: Term -> Term
stripTermPrev (TVar v) = TVar v
stripTermPrev (TFun f ts) = TFun f (map stripTermPrev ts)
stripTermPrev (TPrev t) = stripTermPrev t

nestCPrev :: Int -> Cond -> Cond
nestCPrev 0 c = c
nestCPrev n c = CPrev (nestCPrev (n-1) c)

-- ============================================================
-- Step 3: Expand pattern functions
-- ============================================================

step3 :: [PatternFunc] -> [Rule] -> FreshM [Rule]
step3 pfs rules = do
  let pfRules = map patternFuncToRule pfs
      declaredNames = Set.fromList [n | PatternFunc n _ _ <- pfs]
      conditionalNames = Set.fromList (concatMap rulePatternFuncNames rules)
      pfNames = Set.union declaredNames conditionalNames
      rules' = map lowerPatternFuncResult rules
  if Set.null pfNames
    then return rules'
    else expandRulesFixpoint pfNames (pfRules ++ rules')

-- Step 3's first substep also applies to reductions in implication heads.
-- Step 1 has already exposed every result conjunction, so reductions are
-- direct rule heads here.
rulePatternFuncNames :: Rule -> [Name]
rulePatternFuncNames (Fact r) = resultPatternFuncNames r
rulePatternFuncNames (Rule _ r) = resultPatternFuncNames r

resultPatternFuncNames :: Result -> [Name]
resultPatternFuncNames (RPatternFunc f _ _) = [f]
resultPatternFuncNames (RAlways r) = resultPatternFuncNames r
resultPatternFuncNames (RUntil r _) = resultPatternFuncNames r
resultPatternFuncNames (RAtNext r _) = resultPatternFuncNames r
resultPatternFuncNames (RAnd rs) = concatMap resultPatternFuncNames rs
resultPatternFuncNames (RNext r) = resultPatternFuncNames r
resultPatternFuncNames (RAtom _) = []

lowerPatternFuncResult :: Rule -> Rule
lowerPatternFuncResult (Fact (RPatternFunc f args body)) =
  Fact (RAtom (Atom f (args ++ [body])))
lowerPatternFuncResult (Rule cs (RPatternFunc f args body)) =
  Rule cs (RAtom (Atom f (args ++ [body])))
lowerPatternFuncResult rule = rule

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
needsStep4Cond (CNeg c)  = not (isAtomCond c)
needsStep4Cond (CPrev c) = needsStep4Cond c
needsStep4Cond (CAnd cs) = any needsStep4Cond cs
needsStep4Cond _         = False

isAtomCond :: Cond -> Bool
isAtomCond (CAtom _) = True
isAtomCond _         = False

step4Rule :: Rule -> FreshM [Rule]
step4Rule (Rule cs r) = do
  results <- mapM step4Cond cs
  let (newConds, extraRules) = unzip results
  return (Rule newConds r : concat extraRules)
step4Rule rule = return [rule]

step4Cond :: Cond -> FreshM (Cond, [Rule])
step4Cond (CNeg inner) | not (isAtomCond inner) = do
  let vs = Set.toList (fvCond inner)
      vterms = varsToTerms vs
  p <- freshName "neg"
  let pAtom = Atom p vterms
  return (CNeg (CAtom pAtom), [Rule [inner] (RAtom pAtom)])
step4Cond (CPrev c) = do
  (c', extras) <- step4Cond c
  return (CPrev c', extras)
step4Cond (CAnd cs) = do
  results <- mapM step4Cond cs
  let (cs', extraRules) = unzip results
  return (CAnd cs', concat extraRules)
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

-- | Compatibility wrapper for the original normalization API. Use
-- 'normalizeDetailed' in user-facing tools that need to hide only predicates
-- actually generated by normalization.
normalize :: Program -> Either String ((NormalProgram, Set.Set Name), [String])
normalize source = do
  result <- normalizeDetailed source
  Right
    ( ( normalizedProgram result
      , normalizedPatternFunctions result
      )
    , normalizationWarnings result
    )

-- | Full normalization pipeline: steps 1–5, conversion to 'NormalRule', and
-- exact generated-predicate metadata.
normalizeDetailed :: Program -> Either String NormalizationResult
normalizeDetailed source@(Program rules pfs) = do
  validateProgramSymbols source
  let declaredNames = Set.fromList [n | PatternFunc n _ _ <- pfs]
      conditionalNames = Set.fromList (concatMap rulePatternFuncNames rules)
      pfNames = Set.union declaredNames conditionalNames
      usedIdentifiers = Set.unions
        (map ruleIdentifiers rules ++ map patternFuncIdentifiers pfs)
      (result, _) = runState (runExceptT pipeline)
        (FreshNameGen (freshStart usedIdentifiers))
      pipeline = do
        r1 <- step1 rules
        r2 <- step2 r1
        r3 <- step3 pfs r2
        r3' <- eliminateTermPrevM r3
        r4 <- step4 r3'
        let r5 = step5 r4
        let normals = map toNormalRule r5
        case sequence normals of
          Just ns -> return NormalizationResult
            { normalizedProgram = ns
            , normalizedPatternFunctions = pfNames
            , normalizedAuxiliaryPredicates =
                normalPredicateNames ns `Set.difference` usedIdentifiers
            , normalizationWarnings = validateSafety ns
            }
          Nothing -> throwError $ "Normalization produced non-normal rules:\n" ++
                                  unlines [show r | r <- r5]
      invalidPrevious = any (ruleHasInvalidTermPrev pfNames) rules
                     || any (patternFuncHasInvalidTermPrev pfNames) pfs
  if invalidPrevious
    then Left "Term-level @ is only defined for a term containing a declared pattern-function occurrence"
    else result

normalPredicateNames :: NormalProgram -> Set.Set Name
normalPredicateNames rules = Set.fromList $
  [ atomName (nrHead rule) | rule <- rules ] ++
  [ atomName (ncAtom condition)
  | rule <- rules
  , condition <- nrConditions rule
  ]
  where
    atomName (Atom name _) = name

ruleHasInvalidTermPrev :: Set.Set Name -> Rule -> Bool
ruleHasInvalidTermPrev pfNames (Fact result) = resultHasInvalidTermPrev pfNames result
ruleHasInvalidTermPrev pfNames (Rule conds result) =
  any (condHasInvalidTermPrev pfNames) conds
    || resultHasInvalidTermPrev pfNames result

patternFuncHasInvalidTermPrev :: Set.Set Name -> PatternFunc -> Bool
patternFuncHasInvalidTermPrev pfNames (PatternFunc _ args body) =
  any (termHasInvalidPrev pfNames) (body : args)

resultHasInvalidTermPrev :: Set.Set Name -> Result -> Bool
resultHasInvalidTermPrev pfNames result = case result of
  RAtom atom -> atomHasInvalidTermPrev pfNames atom
  RPatternFunc _ args body -> any (termHasInvalidPrev pfNames) (body : args)
  RAlways inner -> resultHasInvalidTermPrev pfNames inner
  RUntil inner cond -> resultHasInvalidTermPrev pfNames inner
                    || condHasInvalidTermPrev pfNames cond
  RAtNext inner cond -> resultHasInvalidTermPrev pfNames inner
                     || condHasInvalidTermPrev pfNames cond
  RAnd inners -> any (resultHasInvalidTermPrev pfNames) inners
  RNext inner -> resultHasInvalidTermPrev pfNames inner

condHasInvalidTermPrev :: Set.Set Name -> Cond -> Bool
condHasInvalidTermPrev pfNames cond = case cond of
  CAtom atom -> atomHasInvalidTermPrev pfNames atom
  CNeg inner -> condHasInvalidTermPrev pfNames inner
  CPrev inner -> condHasInvalidTermPrev pfNames inner
  CHasBeen inner -> condHasInvalidTermPrev pfNames inner
  COnce inner -> condHasInvalidTermPrev pfNames inner
  CSince left right -> condHasInvalidTermPrev pfNames left
                    || condHasInvalidTermPrev pfNames right
  CAfter left right -> condHasInvalidTermPrev pfNames left
                    || condHasInvalidTermPrev pfNames right
  CFor inner _ -> condHasInvalidTermPrev pfNames inner
  CAnd inners -> any (condHasInvalidTermPrev pfNames) inners
  CEventually inner -> condHasInvalidTermPrev pfNames inner

atomHasInvalidTermPrev :: Set.Set Name -> Atom -> Bool
atomHasInvalidTermPrev pfNames (Atom _ terms) =
  any (termHasInvalidPrev pfNames) terms

termHasInvalidPrev :: Set.Set Name -> Term -> Bool
termHasInvalidPrev _ (TVar _) = False
termHasInvalidPrev pfNames (TFun _ terms) =
  any (termHasInvalidPrev pfNames) terms
termHasInvalidPrev pfNames (TPrev term) =
  not (containsPatternFunction pfNames term) || termHasInvalidPrev pfNames term

containsPatternFunction :: Set.Set Name -> Term -> Bool
containsPatternFunction _ (TVar _) = False
containsPatternFunction pfNames (TFun name terms) =
  name `Set.member` pfNames || any (containsPatternFunction pfNames) terms
containsPatternFunction pfNames (TPrev term) = containsPatternFunction pfNames term

freshStart :: Set.Set String -> Integer
freshStart identifiers =
  case [n | identifier <- Set.toList identifiers, Just n <- [auxSuffix identifier]] of
    [] -> 0
    ns -> maximum ns + 1

auxSuffix :: String -> Maybe Integer
auxSuffix identifier =
  let (digitsReversed, restReversed) = span isAsciiDigit (reverse identifier)
  in if null digitsReversed || take 4 restReversed /= "xua_"
       then Nothing
       else case reads (reverse digitsReversed) of
         [(n, "")] -> Just n
         _ -> Nothing
  where
    isAsciiDigit c = c >= '0' && c <= '9'

ruleIdentifiers :: Rule -> Set.Set String
ruleIdentifiers (Fact r) = resultIdentifiers r
ruleIdentifiers (Rule cs r) =
  Set.union (Set.unions (map condIdentifiers cs)) (resultIdentifiers r)

patternFuncIdentifiers :: PatternFunc -> Set.Set String
patternFuncIdentifiers (PatternFunc f args body) =
  Set.insert f (Set.unions (map termIdentifiers (body : args)))

resultIdentifiers :: Result -> Set.Set String
resultIdentifiers (RAtom a) = atomIdentifiers a
resultIdentifiers (RPatternFunc f args body) =
  Set.insert f (Set.unions (map termIdentifiers (body : args)))
resultIdentifiers (RAlways r) = resultIdentifiers r
resultIdentifiers (RUntil r c) =
  Set.union (resultIdentifiers r) (condIdentifiers c)
resultIdentifiers (RAtNext r c) =
  Set.union (resultIdentifiers r) (condIdentifiers c)
resultIdentifiers (RAnd rs) = Set.unions (map resultIdentifiers rs)
resultIdentifiers (RNext r) = resultIdentifiers r

condIdentifiers :: Cond -> Set.Set String
condIdentifiers (CAtom a) = atomIdentifiers a
condIdentifiers (CNeg c) = condIdentifiers c
condIdentifiers (CPrev c) = condIdentifiers c
condIdentifiers (CHasBeen c) = condIdentifiers c
condIdentifiers (COnce c) = condIdentifiers c
condIdentifiers (CSince c d) =
  Set.union (condIdentifiers c) (condIdentifiers d)
condIdentifiers (CAfter c d) =
  Set.union (condIdentifiers c) (condIdentifiers d)
condIdentifiers (CFor c _) = condIdentifiers c
condIdentifiers (CAnd cs) = Set.unions (map condIdentifiers cs)
condIdentifiers (CEventually c) = condIdentifiers c

atomIdentifiers :: Atom -> Set.Set String
atomIdentifiers (Atom p ts) =
  Set.insert p (Set.unions (map termIdentifiers ts))

termIdentifiers :: Term -> Set.Set String
termIdentifiers (TVar v) = Set.singleton v
termIdentifiers (TFun f ts) =
  Set.insert f (Set.unions (map termIdentifiers ts))
termIdentifiers (TPrev t) = termIdentifiers t

-- | Validate that every variable in a negated condition (at any depth)
-- is bound by at least one positive condition in the same rule.
validateSafety :: NormalProgram -> [String]
validateSafety = concatMap checkRule
  where
    checkRule rule =
      let posVars = Set.unions [fvAtom (ncAtom c) | c <- nrConditions rule, not (ncNegated c)]
          negVars = Set.unions
            [fvAtom (ncAtom c) | c <- nrConditions rule, ncNegated c]
          unsafeVars = negVars `Set.difference` posVars
      in if Set.null unsafeVars
         then []
         else ["Warning: variable(s) " ++ show (Set.toList unsafeVars) ++
               " appear in negated condition(s) but are not bound by any positive condition.\n" ++
               "  Rule: " ++ ppNormalRule rule ++ "\n" ++
               "  Hint: bind variables in positive conditions first, e.g.:\n" ++
               "    r(X) /\\ ~p(X) => q(X).    -- X is bound by r(X) before ~p(X)"]
