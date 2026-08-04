import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Dimension-strict flat-kill legalization rank

The X038 macro processes every Tor--Valabrega defect on a regular carrier by a
lower-dimensional centre-enriched flatification/principalization task.  The
outer coordinate is carrier dimension.  At fixed dimension, unresolved defect
complexity precedes contact and exceptional debt.

This file proves only the well-founded arithmetic of the proposed rank.  It
does not construct the geometric coordinates or prove that an actual
legalization word lowers one of them.
-/

namespace PCRLean
namespace Experimental
namespace FlatKillLegalizationRank

noncomputable section

/-- Carrier dimension, unresolved common-core defects, contact, and debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

/-- Build the four-coordinate rank. -/
def rank (dimension defect contact debt : ℕ) : Rank :=
  toLex (dimension, toLex (defect, toLex (contact, debt)))

/-- A strict carrier-dimension drop dominates arbitrary changes in all later
coordinates. -/
theorem dimension_drop
    {oldDimension newDimension oldDefect newDefect
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newDimension < oldDimension) :
    rank newDimension newDefect newContact newDebt <
      rank oldDimension oldDefect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed dimension, eliminating common-core defect dominates arbitrary
contact and debt changes. -/
theorem defect_drop
    {dimension oldDefect newDefect oldContact newContact oldDebt newDebt : ℕ}
    (h : newDefect < oldDefect) :
    rank dimension newDefect newContact newDebt <
      rank dimension oldDefect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed dimension and defect complexity, contact improvement dominates
arbitrary exceptional-debt changes. -/
theorem contact_drop
    {dimension defect oldContact newContact oldDebt newDebt : ℕ}
    (h : newContact < oldContact) :
    rank dimension defect newContact newDebt <
      rank dimension defect oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier coordinates, debt cleanup is strict. -/
theorem debt_drop
    {dimension defect contact oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank dimension defect contact newDebt <
      rank dimension defect contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)

/-- The complete flat-kill legalization order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end FlatKillLegalizationRank
end Experimental
end PCRLean
