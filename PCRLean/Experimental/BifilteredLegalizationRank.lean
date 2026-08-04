import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Bifiltered transport and legalization rank

The X037 candidate macro first removes the Rees-interchange commutator, then
improves projective-normal passive complexity, then lowers anchor-contact
complexity, and only afterwards cleans exceptional debt.  The order of the
coordinates is essential: a strict drop in an earlier coordinate remains
strict even if every later coordinate grows.

This file proves only the exact well-founded arithmetic of that proposed rank.
It does not construct the geometric coordinates or prove that an ambient
Cartier-trace word lowers one of them.
-/

namespace PCRLean
namespace Experimental
namespace BifilteredLegalizationRank

noncomputable section

/-- Rees commutator, passive regularity, contact, and exceptional debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

/-- Build the four-coordinate legalization rank. -/
def rank (commutator passive contact debt : ℕ) : Rank :=
  toLex (commutator, toLex (passive, toLex (contact, debt)))

/-- A Rees-commutator drop dominates arbitrary changes in all later data. -/
theorem commutator_drop
    {oldCommutator newCommutator oldPassive newPassive
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newCommutator < oldCommutator) :
    rank newCommutator newPassive newContact newDebt <
      rank oldCommutator oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed commutator, passive improvement dominates contact and debt. -/
theorem passive_drop
    {commutator oldPassive newPassive oldContact newContact oldDebt newDebt : ℕ}
    (h : newPassive < oldPassive) :
    rank commutator newPassive newContact newDebt <
      rank commutator oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed commutator and passive complexity, contact improvement dominates
arbitrary exceptional-debt changes. -/
theorem contact_drop
    {commutator passive oldContact newContact oldDebt newDebt : ℕ}
    (h : newContact < oldContact) :
    rank commutator passive newContact newDebt <
      rank commutator passive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier coordinates, ordinary debt cleanup is strict. -/
theorem debt_drop
    {commutator passive contact oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank commutator passive contact newDebt <
      rank commutator passive contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)

/-- The complete bifiltered legalization order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end BifilteredLegalizationRank
end Experimental
end PCRLean
