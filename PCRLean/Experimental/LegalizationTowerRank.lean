import Mathlib
import Mathlib.Data.Prod.Lex
import PCRLean.Experimental.SaturationDebtRank

/-!
# Carrier-dimension legalization towers

Preparatory toroidal or flatifying subcentres cannot be used before they are
jointly legal for the ambient portfolio.  The proposed compiler therefore
legalizes every subcentre recursively.  Recursive calls have strictly smaller
carrier dimension; once the carrier dimension is fixed, the inner
saturation/contact/passive/debt rank controls progress.

This file proves only the well-founded arithmetic of that two-level tower.  It
does not construct a geometric legalization word.
-/

namespace PCRLean
namespace Experimental
namespace LegalizationTowerRank

noncomputable section

/-- Carrier dimension followed by the X037 inner legalization rank. -/
abbrev Rank := ℕ ×ₗ SaturationDebtRank.Rank

/-- Build the complete local legalization rank. -/
def rank
    (carrierDim saturation contact passive debt : ℕ) : Rank :=
  toLex
    (carrierDim,
      SaturationDebtRank.rank saturation contact passive debt)

/-- A recursive call on a strict subcentre dominates every possible change in
its inner packet. -/
theorem carrier_drop
    {oldDim newDim oldS newS oldC newC oldP newP oldD newD : ℕ}
    (hDim : newDim < oldDim) :
    rank newDim newS newC newP newD <
      rank oldDim oldS oldC oldP oldD := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hDim)

/-- At fixed carrier dimension, every strict inner legalization step remains
strict in the complete tower. -/
theorem inner_drop
    {dim : ℕ} {newInner oldInner : SaturationDebtRank.Rank}
    (hInner : newInner < oldInner) :
    toLex (dim, newInner) < toLex (dim, oldInner) := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hInner⟩)

/-- A saturation-debt improvement at fixed carrier dimension is strict. -/
theorem saturation_drop
    {dim oldS newS oldC newC oldP newP oldD newD : ℕ}
    (hS : newS < oldS) :
    rank dim newS newC newP newD <
      rank dim oldS oldC oldP oldD := by
  exact inner_drop (SaturationDebtRank.saturation_drop hS)

/-- The carrier-dimension legalization order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end LegalizationTowerRank
end Experimental
end PCRLean
