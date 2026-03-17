-- |
-- Module      : TemporalProlog.Syntax
-- Description : Abstract syntax tree for Temporal Prolog
--
-- Defines the core AST types for the temporal logic programming language
-- based on Sakuragawa (1986), \"Temporal Prolog\".
--
-- The AST has two levels:
--
-- * __User-facing types__: 'Term', 'Atom', 'Cond', 'Result', 'Rule', and
--   'PatternFunc' represent the full surface syntax including temporal
--   operators (always, until, since, etc.).
--
-- * __Normalized types__: 'NormalCond' and 'NormalRule' represent the
--   restricted normal form where every condition is @\@^m(~?)atom@ and
--   every rule head is a plain atom. See "TemporalProlog.Normalizer".
--
-- 'TPrev' in terms represents the @\@@ operator applied to a value
-- (\"value at previous time\"), while 'CPrev' in conditions represents
-- @\@@ applied to a formula (\"formula held at previous time\").
module TemporalProlog.Syntax where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Variable and functor/predicate names
type Var  = String
type Name = String

-- | Terms: variables, functors, and the previous-time operator on terms
data Term
  = TVar Var
  | TFun Name [Term]
  | TPrev Term          -- @t  (value of t at previous time)
  deriving (Eq, Ord, Show)

-- | Atomic formula: predicate applied to terms
data Atom = Atom Name [Term]
  deriving (Eq, Ord, Show)

-- | Condition formulas (rule bodies)
data Cond
  = CAtom Atom          -- p(t1,...,tk)
  | CNeg Cond            -- ~c
  | CPrev Cond           -- @c
  | CHasBeen Cond        -- #c  (has-been: true from start until now)
  | COnce Cond           -- ?c  (was true at some past time including now)
  | CSince Cond Cond     -- c since d
  | CAfter Cond Cond     -- c after d
  | CFor Cond Int        -- c for n
  | CAnd [Cond]          -- c1 /\ c2 /\ ...
  deriving (Eq, Ord, Show)

-- | Result formulas (rule heads)
data Result
  = RAtom Atom           -- p(t1,...,tk)
  | RAlways Result       -- always r  /  []r
  | RUntil Result Cond   -- r until c
  | RAtNext Result Cond  -- r atnext c
  | RAnd [Result]        -- r1 /\ r2
  deriving (Eq, Ord, Show)

-- | A rule: condition => result, or a bare fact
data Rule
  = Rule [Cond] Result   -- c1 /\ ... /\ cn => r
  | Fact Result           -- r  (unconditional)
  deriving (Eq, Ord, Show)

-- | Pattern function definition: f(t1,...,tk) -> t0
data PatternFunc = PatternFunc Name [Term] Term
  deriving (Eq, Ord, Show)

-- | A program is a collection of rules and pattern function definitions
data Program = Program
  { progRules        :: [Rule]
  , progPatternFuncs :: [PatternFunc]
  } deriving (Eq, Ord, Show)

-- | Normal condition: @^m (~?) atom
data NormalCond = NormalCond
  { ncPrevDepth :: Int    -- number of @ operators
  , ncNegated   :: Bool   -- whether negated
  , ncAtom      :: Atom   -- the atomic formula
  } deriving (Eq, Ord, Show)

-- | Normal rule: c1 /\ ... /\ cn => atom
data NormalRule = NormalRule
  { nrConditions :: [NormalCond]
  , nrHead       :: Atom
  } deriving (Eq, Ord, Show)

-- | A normalized program
type NormalProgram = [NormalRule]

-- | Ground atom (no variables)
type GroundAtom = Atom

-- | A world is a set of ground atoms true at that time step
type World = Set GroundAtom

-- | Substitution: mapping from variables to terms
type Subst = Map Var Term

emptySubst :: Subst
emptySubst = Map.empty

-- | Apply a substitution to a term
applySubstTerm :: Subst -> Term -> Term
applySubstTerm s (TVar v) = case Map.lookup v s of
  Just t  -> t
  Nothing -> TVar v
applySubstTerm s (TFun f ts) = TFun f (map (applySubstTerm s) ts)
applySubstTerm s (TPrev t) = TPrev (applySubstTerm s t)

-- | Apply a substitution to an atom
applySubstAtom :: Subst -> Atom -> Atom
applySubstAtom s (Atom p ts) = Atom p (map (applySubstTerm s) ts)

-- | Apply a substitution to a condition
applySubstCond :: Subst -> Cond -> Cond
applySubstCond s (CAtom a)      = CAtom (applySubstAtom s a)
applySubstCond s (CNeg c)       = CNeg (applySubstCond s c)
applySubstCond s (CPrev c)      = CPrev (applySubstCond s c)
applySubstCond s (CHasBeen c)   = CHasBeen (applySubstCond s c)
applySubstCond s (COnce c)      = COnce (applySubstCond s c)
applySubstCond s (CSince c d)   = CSince (applySubstCond s c) (applySubstCond s d)
applySubstCond s (CAfter c d)   = CAfter (applySubstCond s c) (applySubstCond s d)
applySubstCond s (CFor c n)     = CFor (applySubstCond s c) n
applySubstCond s (CAnd cs)      = CAnd (map (applySubstCond s) cs)

-- | Apply a substitution to a result
applySubstResult :: Subst -> Result -> Result
applySubstResult s (RAtom a)      = RAtom (applySubstAtom s a)
applySubstResult s (RAlways r)    = RAlways (applySubstResult s r)
applySubstResult s (RUntil r c)   = RUntil (applySubstResult s r) (applySubstCond s c)
applySubstResult s (RAtNext r c)  = RAtNext (applySubstResult s r) (applySubstCond s c)
applySubstResult s (RAnd rs)      = RAnd (map (applySubstResult s) rs)

-- | Apply substitution to a normal condition
applySubstNormalCond :: Subst -> NormalCond -> NormalCond
applySubstNormalCond s nc = nc { ncAtom = applySubstAtom s (ncAtom nc) }

-- | Free variables in a term
fvTerm :: Term -> Set Var
fvTerm (TVar v)    = Set.singleton v
fvTerm (TFun _ ts) = Set.unions (map fvTerm ts)
fvTerm (TPrev t)   = fvTerm t

-- | Free variables in an atom
fvAtom :: Atom -> Set Var
fvAtom (Atom _ ts) = Set.unions (map fvTerm ts)

-- | Free variables in a condition
fvCond :: Cond -> Set Var
fvCond (CAtom a)    = fvAtom a
fvCond (CNeg c)     = fvCond c
fvCond (CPrev c)    = fvCond c
fvCond (CHasBeen c) = fvCond c
fvCond (COnce c)    = fvCond c
fvCond (CSince c d) = Set.union (fvCond c) (fvCond d)
fvCond (CAfter c d) = Set.union (fvCond c) (fvCond d)
fvCond (CFor c _)   = fvCond c
fvCond (CAnd cs)    = Set.unions (map fvCond cs)

-- | Free variables in a result
fvResult :: Result -> Set Var
fvResult (RAtom a)     = fvAtom a
fvResult (RAlways r)   = fvResult r
fvResult (RUntil r c)  = Set.union (fvResult r) (fvCond c)
fvResult (RAtNext r c) = Set.union (fvResult r) (fvCond c)
fvResult (RAnd rs)     = Set.unions (map fvResult rs)

-- | Free variables in a rule
fvRule :: Rule -> Set Var
fvRule (Rule cs r) = Set.union (Set.unions (map fvCond cs)) (fvResult r)
fvRule (Fact r)    = fvResult r

-- | Check if a term is ground (no variables)
isGroundTerm :: Term -> Bool
isGroundTerm (TVar _)    = False
isGroundTerm (TFun _ ts) = all isGroundTerm ts
isGroundTerm (TPrev t)   = isGroundTerm t

-- | Check if an atom is ground
isGroundAtom :: Atom -> Bool
isGroundAtom (Atom _ ts) = all isGroundTerm ts

-- | Compose two substitutions: apply s2 then s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.union (Map.map (applySubstTerm s1) s2) s1
