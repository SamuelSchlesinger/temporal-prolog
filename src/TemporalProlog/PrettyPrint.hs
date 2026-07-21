-- |
-- Module      : TemporalProlog.PrettyPrint
-- Description : Human-readable display for all AST types
--
-- Pretty-prints terms, atoms, conditions, results, rules, and their
-- normalized counterparts. Uses ASCII operator syntax. Handles special
-- display for lists (@[H|T]@, @[a, b, c]@), infix operators (@X > 5@),
-- and the @\@@ prefix.
module TemporalProlog.PrettyPrint
  ( ppTerm
  , ppAtom
  , ppCond
  , ppResult
  , ppRule
  , ppNormalCond
  , ppNormalRule
  , ppProgram
  , ppPatternFunc
  , ppNormalProgram
  ) where

import Data.List (intercalate)
import TemporalProlog.Syntax

-- | Render a well-formed term as parseable source syntax.
ppTerm :: Term -> String
ppTerm (TVar v)      = v
ppTerm (TFun "[]" []) = "[]"
ppTerm (TFun f [])   = f
ppTerm (TFun "." [h, t]) = "[" ++ ppTerm h ++ ppListTail t ++ "]"
ppTerm (TFun "+" [l, r]) = ppTermAtom l ++ " + " ++ ppTermAtom r
ppTerm (TFun "-" [l, r]) = ppTermAtom l ++ " - " ++ ppTermAtom r
ppTerm (TFun "*" [l, r]) = ppTermAtom l ++ " * " ++ ppTermAtom r
ppTerm (TFun "div" [l, r]) = ppTermAtom l ++ " div " ++ ppTermAtom r
ppTerm (TFun "mod" [l, r]) = ppTermAtom l ++ " mod " ++ ppTermAtom r
ppTerm (TFun f ts)   = f ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"
ppTerm (TPrev t)     = "@" ++ ppTermAtom t

ppTermAtom :: Term -> String
ppTermAtom t@(TFun "+" _) = "(" ++ ppTerm t ++ ")"
ppTermAtom t@(TFun "-" [_, _]) = "(" ++ ppTerm t ++ ")"
ppTermAtom t@(TFun "*" _) = "(" ++ ppTerm t ++ ")"
ppTermAtom t@(TFun "div" [_, _]) = "(" ++ ppTerm t ++ ")"
ppTermAtom t@(TFun "mod" [_, _]) = "(" ++ ppTerm t ++ ")"
ppTermAtom t@(TFun _ (_:_)) = ppTerm t
ppTermAtom t@(TVar _)       = ppTerm t
ppTermAtom t@(TFun _ [])    = ppTerm t
ppTermAtom t                = "(" ++ ppTerm t ++ ")"

ppListTail :: Term -> String
ppListTail (TFun "[]" [])    = ""
ppListTail (TFun "." [h, t]) = ", " ++ ppTerm h ++ ppListTail t
ppListTail t                  = " | " ++ ppTerm t

-- | Render an atom, using infix syntax for built-in binary relations.
ppAtom :: Atom -> String
ppAtom (Atom "=" [l, r])  = ppTerm l ++ " = " ++ ppTerm r
ppAtom (Atom "is" [l, r]) = ppTerm l ++ " is " ++ ppTerm r
ppAtom (Atom ">" [l, r])  = ppTerm l ++ " > " ++ ppTerm r
ppAtom (Atom "<" [l, r])  = ppTerm l ++ " < " ++ ppTerm r
ppAtom (Atom ">=" [l, r]) = ppTerm l ++ " >= " ++ ppTerm r
ppAtom (Atom "<=" [l, r]) = ppTerm l ++ " <= " ++ ppTerm r
ppAtom (Atom p [])         = p
ppAtom (Atom p ts)         = p ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"

-- | Render a condition with parentheses that preserve its exact syntax tree.
ppCond :: Cond -> String
ppCond (CAtom a)    = ppAtom a
ppCond (CNeg c)     = "~" ++ ppCondAtom c
ppCond (CPrev c)    = "@" ++ ppCondAtom c
ppCond (CHasBeen c) = "#" ++ ppCondAtom c
ppCond (COnce c)    = "?" ++ ppCondAtom c
ppCond (CSince c d) = ppCondAtom c ++ " since " ++ ppCondAtom d
ppCond (CAfter c d) = ppCondAtom c ++ " after " ++ ppCondAtom d
ppCond (CFor c n)   = ppCondAtom c ++ " for " ++ show n
ppCond (CEventually c) = "eventually " ++ ppCondAtom c
ppCond (CAnd cs)    = intercalate " /\\ " (map ppCondAtom cs)

ppCondAtom :: Cond -> String
ppCondAtom c@(CAtom _) = ppCond c
ppCondAtom c@(CNeg _)  = ppCond c
ppCondAtom c@(CPrev _) = ppCond c
ppCondAtom c            = "(" ++ ppCond c ++ ")"

-- | Render a result formula with precedence-preserving parentheses.
ppResult :: Result -> String
ppResult (RAtom a)     = ppAtom a
ppResult (RPatternFunc f args body) =
  f ++ "(" ++ intercalate ", " (map ppTerm args) ++ ") -> " ++ ppTerm body
ppResult (RAlways r)   = "always " ++ ppResultAtom r
ppResult (RUntil r c)  = ppResultAtom r ++ " until " ++ ppCondAtom c
ppResult (RAtNext r c) = ppResultAtom r ++ " atnext " ++ ppCondAtom c
ppResult (RNext r)     = "next " ++ ppResultAtom r
ppResult (RAnd rs)     = intercalate " /\\ " (map ppResultAtom rs)

ppResultAtom :: Result -> String
ppResultAtom r@(RAtom _) = ppResult r
ppResultAtom r            = "(" ++ ppResult r ++ ")"

-- | Render a source rule, including its terminating period.
ppRule :: Rule -> String
ppRule (Rule cs r) = intercalate " /\\ " (map ppCondAtom cs) ++ " => " ++ ppResult r ++ "."
ppRule (Fact r)    = ppResult r ++ "."

-- | Render a normal-form condition.
ppNormalCond :: NormalCond -> String
ppNormalCond (NormalCond d neg a) =
  let prevs = replicate d '@'
      negStr = if neg then "~" else ""
  in prevs ++ negStr ++ ppAtom a

-- | Render a normal-form rule, including its terminating period.
ppNormalRule :: NormalRule -> String
ppNormalRule (NormalRule [] h) = ppAtom h ++ "."
ppNormalRule (NormalRule cs h) =
  intercalate " /\\ " (map ppNormalCond cs) ++ " => " ++ ppAtom h ++ "."

-- | Render a complete source program with one item per line.
ppProgram :: Program -> String
ppProgram prog = unlines $
  map ppPatternFunc (progPatternFuncs prog) ++
  map ppRule (progRules prog)

-- | Render a pattern-function definition, including its terminating period.
ppPatternFunc :: PatternFunc -> String
ppPatternFunc (PatternFunc f args body) =
  f ++ "(" ++ intercalate ", " (map ppTerm args) ++ ") -> " ++ ppTerm body ++ "."

-- | Render a complete normal-form program with one rule per line.
ppNormalProgram :: NormalProgram -> String
ppNormalProgram = unlines . map ppNormalRule
