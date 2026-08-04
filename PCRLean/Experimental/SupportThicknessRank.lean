import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# The support-thickness rank

A nonregular scheme-theoretic intersection has two conceptually different
failure modes.

* Its reduced support can still be singular.  This is a genuinely
  lower-dimensional geometric task.
* Its reduced support can be regular while the intersection remains a
  nonreduced or non-quasi-regular thickening.  This is a finite thickness,
  contact, Hasse, or Fitting task on a regular carrier.

The first two coordinates of the proposed global rank are therefore the
lexicographic pair

`(support dimension, thickness/contact complexity)`.

The arithmetic below proves the two strict-drop constructors.  It does not
construct the geometric successor or prove that every bad stratum enters one
of these strict branches; those are separate edge obligations.
-/

namespace PCRLean
namespace Experimental
namespace SupportThicknessRank

noncomputable section

/-- Lexicographic support-dimension / thickness rank. -/
abbrev Rank := ℕ ×ₗ ℕ

/-- Build the two-coordinate rank. -/
def mkRank (supportDim thickness : ℕ) : Rank :=
  toLex (supportDim, thickness)

/-- Any strict drop of the support dimension dominates all changes in the
thickness coordinate. -/
theorem support_drop
    {newDim oldDim newThickness oldThickness : ℕ}
    (hDim : newDim < oldDim) :
    mkRank newDim newThickness < mkRank oldDim oldThickness := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hDim)

/-- At fixed support dimension, a strict thickness/contact drop is strict in
the lexicographic rank. -/
theorem thickness_drop
    {dim newThickness oldThickness : ℕ}
    (hThickness : newThickness < oldThickness) :
    mkRank dim newThickness < mkRank dim oldThickness := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, hThickness⟩)

/-- The support-thickness order is well founded because both coordinates are
natural numbers with their usual well-founded order. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end SupportThicknessRank
end Experimental
end PCRLean
