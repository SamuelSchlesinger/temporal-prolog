-- |
-- Module      : TemporalProlog.Unification
-- Description : Term unification and one-way matching
--
-- Implements Robinson unification with occurs check for 'Term' values,
-- and one-way matching used by the interpreter to match rule patterns
-- against ground atoms in a world.
--
-- 'unifyTerm' finds a most general unifier for two terms. 'matchAtom'
-- performs one-directional matching where only variables in the first
-- (pattern) argument are bound — the second argument is treated as ground.
--
-- Both operations handle 'TPrev' structurally: @\@t1@ unifies with @\@t2@
-- if @t1@ unifies with @t2@.
module TemporalProlog.Unification where

import qualified Data.Map.Strict as Map
import TemporalProlog.Syntax

-- | Unify two terms, returning a most general unifier if one exists.
unifyTerm :: Term -> Term -> Maybe Subst
unifyTerm (TVar v) t = bindVar v t
unifyTerm t (TVar v) = bindVar v t
unifyTerm (TFun f fs) (TFun g gs)
  | f == g && length fs == length gs = unifyTerms fs gs
  | otherwise = Nothing
unifyTerm (TPrev t1) (TPrev t2) = unifyTerm t1 t2
unifyTerm _ _ = Nothing

-- | Bind a variable to a term, with occurs check.
bindVar :: Var -> Term -> Maybe Subst
bindVar v (TVar w) | v == w = Just emptySubst
bindVar v t
  | occursIn v t = Nothing
  | otherwise    = Just (Map.singleton v t)

-- | Occurs check: does variable v occur in term t?
occursIn :: Var -> Term -> Bool
occursIn v (TVar w)    = v == w
occursIn v (TFun _ ts) = any (occursIn v) ts
occursIn v (TPrev t)   = occursIn v t

-- | Unify two lists of terms pairwise.
unifyTerms :: [Term] -> [Term] -> Maybe Subst
unifyTerms [] [] = Just emptySubst
unifyTerms (t1:ts1) (t2:ts2) = do
  s1 <- unifyTerm t1 t2
  s2 <- unifyTerms (map (applySubstTerm s1) ts1) (map (applySubstTerm s1) ts2)
  return (composeSubst s2 s1)
unifyTerms _ _ = Nothing

-- | Unify two atoms.
unifyAtom :: Atom -> Atom -> Maybe Subst
unifyAtom (Atom p ts1) (Atom q ts2)
  | p == q && length ts1 == length ts2 = unifyTerms ts1 ts2
  | otherwise = Nothing

-- | Match a pattern atom against a ground atom.
--   Like unification but only substitutes variables in the pattern (first arg).
matchAtom :: Atom -> Atom -> Maybe Subst
matchAtom (Atom p ts1) (Atom q ts2)
  | p == q && length ts1 == length ts2 = matchTerms ts1 ts2
  | otherwise = Nothing

matchTerms :: [Term] -> [Term] -> Maybe Subst
matchTerms [] [] = Just emptySubst
matchTerms (t1:ts1) (t2:ts2) = do
  s1 <- matchTerm t1 t2
  s2 <- matchTerms (map (applySubstTerm s1) ts1) ts2
  return (composeSubst s2 s1)
matchTerms _ _ = Nothing

matchTerm :: Term -> Term -> Maybe Subst
matchTerm (TVar v) t = Just (Map.singleton v t)
matchTerm (TFun f fs) (TFun g gs)
  | f == g && length fs == length gs = matchTerms fs gs
matchTerm (TPrev t1) (TPrev t2) = matchTerm t1 t2
matchTerm t1 t2
  | t1 == t2  = Just emptySubst
  | otherwise = Nothing
