import Mathlib

/-!
# Nilpotent support-thickness certificates

Let `K ≤ J` be ideals with the same underlying support, so geometrically
`V(J)` is the reduced carrier of the thickened intersection `V(K)`.  The
condition

`J^e ≤ K`

says that the nilpotent ideal `J/K` is killed at thickness level `e`.
Noetherian geometry supplies such an exponent after radical equality, but the
existence theorem and its behavior under blowup are separate scheme-level
obligations.

This file records the exact elementary algebra used by the X035
support-thickness rank.
-/

namespace PCRLean
namespace Experimental
namespace NilpotentThickness

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The reduced-carrier ideal `J` is killed modulo the thickening ideal `K` at
level `e`. -/
def KilledAt (K J : Ideal R) (e : ℕ) : Prop :=
  J ^ e ≤ K

/-- Once killed, the thickness remains killed at every larger exponent. -/
theorem killedAt_mono
    {K J : Ideal R} {e f : ℕ}
    (hkill : KilledAt K J e)
    (hef : e ≤ f) :
    KilledAt K J f := by
  exact (Ideal.pow_le_pow_right hef).trans hkill

/-- Killing at exponent one collapses the thickening whenever `K ≤ J`. -/
theorem eq_of_killedAt_one
    {K J : Ideal R}
    (hKJ : K ≤ J)
    (hkill : KilledAt K J 1) :
    K = J := by
  apply le_antisymm hKJ
  simpa [KilledAt] using hkill

/-- A genuine thickening cannot be killed at exponent one. -/
theorem not_killedAt_one_of_ne
    {K J : Ideal R}
    (hKJ : K ≤ J)
    (hne : K ≠ J) :
    ¬ KilledAt K J 1 := by
  intro h
  exact hne (eq_of_killedAt_one hKJ h)

/-- A certified strict drop of the numerical thickness level. -/
structure StrictDrop (oldLevel newLevel : ℕ) : Prop where
  drop : newLevel < oldLevel

/-- Strict thickness drops compose. -/
theorem StrictDrop.trans
    {a b c : ℕ}
    (hab : StrictDrop a b)
    (hbc : StrictDrop b c) :
    StrictDrop a c :=
  ⟨hbc.drop.trans hab.drop⟩

end

end NilpotentThickness
end Experimental
end PCRLean
