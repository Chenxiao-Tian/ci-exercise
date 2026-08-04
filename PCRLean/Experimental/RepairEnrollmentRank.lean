import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Repair-owner enrollment and Cartier-trace debt rank

A module being flatified cannot be treated as an already passive owner.  The
local macro first works in a repair phase, consumes finite source-labelled
Cartier/contact debt, and then either enrolls the repaired module as passive or
discharges a zero defect.

The proposed local ordering is

```text
carrier dimension
> number of unresolved repair owners
> total trace debt
> contact debt
> ordinary exceptional debt.
```

A promotion or zero discharge lowers the second coordinate; one trace-cleaning
step lowers the third.  Earlier drops dominate arbitrary changes in all later
coordinates.  This file proves only the exact well-founded arithmetic.  It does
not construct repair owners, flatifiers, trace centres, or geometric descent.
-/

namespace PCRLean
namespace Experimental
namespace RepairEnrollmentRank

noncomputable section

/-- Carrier dimension, repair-owner count, trace debt, contact, and debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)))

/-- Build the repair-enrollment rank. -/
def rank
    (dimension repairs traceDebt contact debt : ℕ) : Rank :=
  toLex
    (dimension,
      toLex (repairs, toLex (traceDebt, toLex (contact, debt))))

/-- Recursive carrier legalization strictly lowers dimension. -/
theorem dimension_drop
    {oldDimension newDimension oldRepairs newRepairs oldTrace newTrace
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newDimension < oldDimension) :
    rank newDimension newRepairs newTrace newContact newDebt <
      rank oldDimension oldRepairs oldTrace oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Repair-to-passive promotion or zero discharge lowers the unresolved repair
count and dominates arbitrary changes in all debt coordinates. -/
theorem enrollment_drop
    {dimension oldRepairs newRepairs oldTrace newTrace
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newRepairs < oldRepairs) :
    rank dimension newRepairs newTrace newContact newDebt <
      rank dimension oldRepairs oldTrace oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed carrier and repair phase, consuming source-labelled trace debt is
strict even if contact and ordinary debt are relabelled. -/
theorem trace_drop
    {dimension repairs oldTrace newTrace oldContact newContact oldDebt newDebt : ℕ}
    (h : newTrace < oldTrace) :
    rank dimension repairs newTrace newContact newDebt <
      rank dimension repairs oldTrace oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier coordinates, contact cleaning is strict. -/
theorem contact_drop
    {dimension repairs trace oldContact newContact oldDebt newDebt : ℕ}
    (h : newContact < oldContact) :
    rank dimension repairs trace newContact newDebt <
      rank dimension repairs trace oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)⟩)

/-- Ordinary debt cleanup is the final strict coordinate. -/
theorem debt_drop
    {dimension repairs trace contact oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank dimension repairs trace contact newDebt <
      rank dimension repairs trace contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)⟩)

/-- The complete repair-enrollment order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end RepairEnrollmentRank
end Experimental
end PCRLean
