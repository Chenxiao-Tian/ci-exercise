import Mathlib
import PCRLean.Experimental.CriticalPairTorExcess

/-!
# Tor independence is the zero-excess condition, not the clean-intersection condition

X033 isolated the ideal equality `I ⊓ J = I * J`.  This file records the
sharp order-theoretic boundary needed by the next geometric refinement.
For nested ideals `I ≤ J`, the equality is equivalent to `I = I * J`.
Consequently every nested non-idempotent pair has nonzero Tor excess.

Regular nested centres are nevertheless clean in the geometric sense.  Thus
Tor independence may be used as the transverse/zero-excess subchamber, but it
cannot be used as the universal legality gate for wonderful serialization.
The geometric clean-excess theorem is a separate edge.
-/

namespace PCRLean
namespace Experimental
namespace TorExcessIsZeroExcess

noncomputable section

universe u

variable {R : Type u} [CommRing R]

open CriticalPairTorExcess

/-- In a nested pair, Tor independence is exactly the absorption identity
`I = I * J`. -/
theorem torIndependent_nested_iff
    {I J : Ideal R} (hIJ : I ≤ J) :
    TorIndependent I J ↔ I = I * J := by
  simp [TorIndependent, inf_eq_left.mpr hIJ]

/-- A centre paired with itself is Tor independent exactly when its ideal is
idempotent. -/
theorem torIndependent_same_iff
    (I : Ideal R) :
    TorIndependent I I ↔ I = I * I := by
  simpa using torIndependent_nested_iff (I := I) (J := I) le_rfl

/-- Exact no-go boundary: nested non-idempotent ideals necessarily have Tor
excess. -/
theorem not_torIndependent_of_nested_nonidempotent
    {I J : Ideal R} (hIJ : I ≤ J) (hne : I ≠ I * J) :
    ¬ TorIndependent I J := by
  intro h
  exact hne ((torIndependent_nested_iff hIJ).mp h)

/-- The same-centre version of the no-go theorem. -/
theorem not_torIndependent_of_nonidempotent
    {I : Ideal R} (hne : I ≠ I * I) :
    ¬ TorIndependent I I := by
  exact not_torIndependent_of_nested_nonidempotent le_rfl hne

end

end TorExcessIsZeroExcess
end Experimental
end PCRLean
