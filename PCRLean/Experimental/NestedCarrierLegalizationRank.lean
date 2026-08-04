import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Dimension-strict carrier-legalization rank

The X039 compiler chooses one centre-enriched flatifier for a raw carrier.
Every regular centre in a word dominating that flatifier is legalized
recursively on a carrier of strictly smaller dimension.  At fixed dimension,
the remaining word height decreases.  Only after the nested word is exhausted
do the outer Rees-defect, contact, and debt coordinates govern progress.

This file proves only the exact well-founded arithmetic.  It does not construct
a flatifier, a regular factorization word, or a geometric strict-drop
certificate.
-/

namespace PCRLean
namespace Experimental
namespace NestedCarrierLegalizationRank

noncomputable section

/-- Carrier dimension, remaining flatifier-word height, unresolved Rees defect,
contact, and debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)))

/-- Build the five-coordinate nested legalization rank. -/
def rank
    (carrierDim wordHeight reesDefect contact debt : ℕ) : Rank :=
  toLex (carrierDim,
    toLex (wordHeight,
      toLex (reesDefect,
        toLex (contact, debt))))

/-- A recursive call on a proper carrier dominates arbitrary later changes. -/
theorem carrier_dimension_drop
    {oldDim newDim oldHeight newHeight oldDefect newDefect
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newDim < oldDim) :
    rank newDim newHeight newDefect newContact newDebt <
      rank oldDim oldHeight oldDefect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed carrier dimension, consuming one step of the immutable regular
flatifier word is strict. -/
theorem word_height_drop
    {dim oldHeight newHeight oldDefect newDefect
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newHeight < oldHeight) :
    rank dim newHeight newDefect newContact newDebt <
      rank dim oldHeight oldDefect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- After the carrier word is fixed, a Rees comparison improvement is strict. -/
theorem rees_defect_drop
    {dim height oldDefect newDefect
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newDefect < oldDefect) :
    rank dim height newDefect newContact newDebt <
      rank dim height oldDefect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier coordinates, contact improvement dominates debt. -/
theorem contact_drop
    {dim height defect oldContact newContact oldDebt newDebt : ℕ}
    (h : newContact < oldContact) :
    rank dim height defect newContact newDebt <
      rank dim height defect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)⟩)

/-- At fixed earlier coordinates, debt cleanup is strict. -/
theorem debt_drop
    {dim height defect contact oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank dim height defect contact newDebt <
      rank dim height defect contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)⟩)

/-- The nested carrier-legalization order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end NestedCarrierLegalizationRank
end Experimental
end PCRLean
