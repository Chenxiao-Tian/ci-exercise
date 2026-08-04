import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Saturation-debt rank

After a flatifying modification of a carrier, the actual ambient transform may
differ from the flat strict-transform target by coherent exceptional-power
torsion.  The primary legalization coordinate is therefore the exceptional
saturation debt.  Contact, residual passive-flatness complexity, and ordinary
exceptional debt follow it.

The coordinate order is essential: consuming an exceptional saturation layer
must remain strict even if the ambient blowup creates younger boundary or debt
labels.  This file proves only the well-founded arithmetic of that proposed
rank.
-/

namespace PCRLean
namespace Experimental
namespace SaturationDebtRank

noncomputable section

/-- Saturation debt, contact debt, passive defect, then ordinary debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

/-- Build the four-coordinate rank. -/
def rank (saturation contact passive debt : ℕ) : Rank :=
  toLex (saturation, toLex (contact, toLex (passive, debt)))

/-- A strict saturation drop dominates arbitrary later-coordinate changes. -/
theorem saturation_drop
    {oldS newS oldC newC oldP newP oldD newD : ℕ}
    (h : newS < oldS) :
    rank newS newC newP newD < rank oldS oldC oldP oldD := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed saturation debt, a contact drop dominates passive and ordinary
debt changes. -/
theorem contact_drop
    {s oldC newC oldP newP oldD newD : ℕ}
    (h : newC < oldC) :
    rank s newC newP newD < rank s oldC oldP oldD := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed saturation and contact, passive legalization is strict. -/
theorem passive_drop
    {s c oldP newP oldD newD : ℕ}
    (h : newP < oldP) :
    rank s c newP newD < rank s c oldP oldD := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- Ordinary debt cleanup is the final strict coordinate. -/
theorem debt_drop
    {s c p oldD newD : ℕ}
    (h : newD < oldD) :
    rank s c p newD < rank s c p oldD := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)

/-- The saturation-debt order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end SaturationDebtRank
end Experimental
end PCRLean
