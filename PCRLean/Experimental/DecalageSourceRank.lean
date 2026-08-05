import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Saturated-décalage source rank

The proposed X041 macro is ordered by carrier dimension, exceptional
power-torsion exponent, unresolved source-capsule count, and ordinary debt.
A drop in an earlier coordinate dominates arbitrary changes in all later
coordinates.  The exact arithmetic is independent of the geometric theorem
that must force one of these drops.
-/

namespace PCRLean
namespace Experimental
namespace DecalageSourceRank

noncomputable section

/-- Carrier dimension, décalage/torsion height, source count, and debt. -/
abbrev Rank := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

/-- Build the four-coordinate rank. -/
def rank (carrierDim torsionHeight sourceCount debt : ℕ) : Rank :=
  toLex (carrierDim, toLex (torsionHeight, toLex (sourceCount, debt)))

/-- Lower carrier dimension dominates every later change. -/
theorem carrier_drop
    {oldDim newDim oldHeight newHeight oldSources newSources oldDebt newDebt : ℕ}
    (h : newDim < oldDim) :
    rank newDim newHeight newSources newDebt <
      rank oldDim oldHeight oldSources oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed dimension, one Cartier-décalage layer is a strict drop. -/
theorem torsion_drop
    {dim oldHeight newHeight oldSources newSources oldDebt newDebt : ℕ}
    (h : newHeight < oldHeight) :
    rank dim newHeight newSources newDebt <
      rank dim oldHeight oldSources oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed geometric and torsion data, consuming a source capsule is strict. -/
theorem source_drop
    {dim height oldSources newSources oldDebt newDebt : ℕ}
    (h : newSources < oldSources) :
    rank dim height newSources newDebt <
      rank dim height oldSources oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier coordinates, debt cleanup is strict. -/
theorem debt_drop
    {dim height sources oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank dim height sources newDebt <
      rank dim height sources oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)

/-- The complete proposed order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end DecalageSourceRank
end Experimental
end PCRLean
