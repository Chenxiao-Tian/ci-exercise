import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Carrier/source/flag rank

The X041 legalization macro first lowers the support dimension of the common
functorial flatifier, then consumes unresolved source-word packages, then lowers
nested regular-flag depth, and finally executes the remaining common word.
Earlier-coordinate progress dominates arbitrary later changes.

This file proves only the well-founded arithmetic.  Geometry must still prove
that every actual nonterminal macro enters one of the strict branches.
-/

namespace PCRLean
namespace Experimental
namespace HomogenizedCarrierRank

noncomputable section

/-- Common support dimension, unresolved source packages, nested flag depth,
and remaining word height. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

/-- Build the four-coordinate rank. -/
def rank (supportDim sources flagDepth wordHeight : ℕ) : Rank :=
  toLex (supportDim, toLex (sources, toLex (flagDepth, wordHeight)))

/-- A support-dimension drop dominates all later coordinates. -/
theorem support_drop
    {oldDim newDim oldSources newSources oldFlag newFlag oldWord newWord : ℕ}
    (h : newDim < oldDim) :
    rank newDim newSources newFlag newWord <
      rank oldDim oldSources oldFlag oldWord := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed support dimension, consuming source packages is strict. -/
theorem source_drop
    {dim oldSources newSources oldFlag newFlag oldWord newWord : ℕ}
    (h : newSources < oldSources) :
    rank dim newSources newFlag newWord <
      rank dim oldSources oldFlag oldWord := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed support and source count, nested flag-depth descent is strict. -/
theorem flag_drop
    {dim sources oldFlag newFlag oldWord newWord : ℕ}
    (h : newFlag < oldFlag) :
    rank dim sources newFlag newWord <
      rank dim sources oldFlag oldWord := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier data, one common-word edge is strict. -/
theorem word_drop
    {dim sources flag oldWord newWord : ℕ}
    (h : newWord < oldWord) :
    rank dim sources flag newWord < rank dim sources flag oldWord := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)

/-- The complete carrier/source/flag rank is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end HomogenizedCarrierRank
end Experimental
end PCRLean
