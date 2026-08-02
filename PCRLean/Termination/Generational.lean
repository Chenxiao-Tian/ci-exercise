import Mathlib

/-!
# Finite-source generational descent

This file formalizes the lexicographic rank used by the restricted
finite-source generation chamber.  It proves well-foundedness and the exact
rank edges for financed births, source merges, cleanup, and internal macro
steps.  It does not assert the open geometric birth-trichotomy theorem.
-/

namespace PCRLean.Termination.Generational

/-- `U` is remaining carrier height, `A` the active identity count, and
`beta` the remaining cleanup-macro height. -/
abbrev GenRank := ℕ × (ℕ × ℕ)

/-- Lexicographic descent on `(U,A,beta)`. -/
abbrev GenLt : GenRank → GenRank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)

/-- The generational rank is well founded. -/
theorem genLt_wellFounded : WellFounded GenLt :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

/-- A financed birth may reset later coordinates, but must consume carrier
height. -/
theorem financedBirth_lt
    {U' U A' A beta' beta : ℕ} (hU : U' < U) :
    GenLt (U', (A', beta')) (U, (A, beta)) :=
  Prod.Lex.left (A', beta') (A, beta) hU

/-- A source merge preserves carrier height and strictly lowers the active
identity count. -/
theorem sourceMerge_lt
    {U A' A beta' beta : ℕ} (hA : A' < A) :
    GenLt (U, (A', beta')) (U, (A, beta)) :=
  Prod.Lex.right U (Prod.Lex.left beta' beta hA)

/-- Cleanup has the same lexicographic contract as a source merge. -/
theorem cleanup_lt
    {U A' A beta' beta : ℕ} (hA : A' < A) :
    GenLt (U, (A', beta')) (U, (A, beta)) :=
  sourceMerge_lt hA

/-- An internal finite macro step preserves the outer coordinates and lowers
only the macro remainder. -/
theorem macroInternal_lt
    {U A beta' beta : ℕ} (hbeta : beta' < beta) :
    GenLt (U, (A, beta')) (U, (A, beta)) :=
  Prod.Lex.right U (Prod.Lex.right A hbeta)

/-- Consuming `r >= 2` active parents and replacing them by one child lowers
active count by at least one. -/
theorem merge_count_strict_drop {A r : ℕ} (hr2 : 2 ≤ r) (hrA : r ≤ A) :
    A - r + 1 < A := by
  omega

/-- Consuming one available carrier coupon strictly lowers carrier height. -/
theorem coupon_strict_drop {U : ℕ} (hU : 0 < U) : U - 1 < U := by
  omega

end PCRLean.Termination.Generational
