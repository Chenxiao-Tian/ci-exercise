import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Common flatifier support-budget rank

X040 aggregates the finite orbit of maximal-carrier flatifier trace ideals into
one symmetry-invariant product ideal.  Its internal realization is ranked first
by the dimension of the product support, then by the number of unresolved
source factors, and finally by the remaining regular-word height.

A support-dimension drop dominates all later changes.  At fixed support
dimension, consuming one source factor dominates changes in word height.  At
fixed earlier coordinates, executing one word edge is strict.

This file proves only the well-founded arithmetic.  It does not construct the
product blowup, a regular principalization word, or a resolution algorithm.
-/

namespace PCRLean
namespace Experimental
namespace CommonFlatifierBudgetRank

noncomputable section

/-- Support dimension, unresolved source count, remaining common-word height. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ ℕ)

/-- Build the common-flatifier rank. -/
def rank (supportDim unresolvedSources wordHeight : ℕ) : Rank :=
  toLex (supportDim, toLex (unresolvedSources, wordHeight))

/-- Lower support dimension is strict regardless of later coordinates. -/
theorem support_drop
    {oldDim newDim oldSources newSources oldHeight newHeight : ℕ}
    (h : newDim < oldDim) :
    rank newDim newSources newHeight <
      rank oldDim oldSources oldHeight := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed support dimension, consuming source obligations is strict. -/
theorem source_drop
    {dim oldSources newSources oldHeight newHeight : ℕ}
    (h : newSources < oldSources) :
    rank dim newSources newHeight < rank dim oldSources oldHeight := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed support and source count, one word edge is strict. -/
theorem word_drop
    {dim sources oldHeight newHeight : ℕ}
    (h : newHeight < oldHeight) :
    rank dim sources newHeight < rank dim sources oldHeight := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)

/-- The complete common-flatifier rank is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end CommonFlatifierBudgetRank
end Experimental
end PCRLean
