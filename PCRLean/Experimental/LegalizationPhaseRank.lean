import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Contact--passive--debt legalization rank

The X036 macro first removes genuine anchor-contact complexity, then flattens
the finite projective-normal passive packet, and only afterwards cleans the
remaining exceptional debt.  The order of coordinates is essential: a contact
or passive improvement must remain strict even if a preparatory blowup creates
new exceptional labels.

This file proves the well-founded arithmetic of the proposed three-coordinate
rank.  Geometry must still prove that each actual ambient macro enters one of
these strict branches.
-/

namespace PCRLean
namespace Experimental
namespace LegalizationPhaseRank

noncomputable section

/-- Contact order, then unresolved passive-flatness complexity, then debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ ℕ)

/-- Build the three-coordinate legalization rank. -/
def rank (contact passive debt : ℕ) : Rank :=
  toLex (contact, toLex (passive, debt))

/-- A contact drop dominates arbitrary changes in passive complexity and debt. -/
theorem contact_drop
    {oldContact newContact oldPassive newPassive oldDebt newDebt : ℕ}
    (hContact : newContact < oldContact) :
    rank newContact newPassive newDebt <
      rank oldContact oldPassive oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hContact)

/-- At fixed contact order, a passive-flatness drop dominates arbitrary debt
changes. -/
theorem passive_drop
    {contact oldPassive newPassive oldDebt newDebt : ℕ}
    (hPassive : newPassive < oldPassive) :
    rank contact newPassive newDebt <
      rank contact oldPassive oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hPassive)⟩)

/-- At fixed contact and passive coordinates, debt cleanup is strict. -/
theorem debt_drop
    {contact passive oldDebt newDebt : ℕ}
    (hDebt : newDebt < oldDebt) :
    rank contact passive newDebt <
      rank contact passive oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hDebt⟩)⟩)

/-- The complete legalization order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end LegalizationPhaseRank
end Experimental
end PCRLean
