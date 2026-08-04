import Mathlib

/-!
# Projective surjections split

Every surjective linear map onto a projective module has a linear right inverse.
-/

namespace PCRLean
namespace Experimental
namespace ProjectiveSurjectionSplitAtomic

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [AddCommGroup F] [Module R F]
variable {P : Type w} [AddCommGroup P] [Module R P]
variable [Module.Projective R P]

/-- Projective lifting applied to the identity gives a section. -/
theorem projective_surjection_splits
    (q : F →ₗ[R] P) (hq : Function.Surjective q) :
    ∃ s : P →ₗ[R] F, q.comp s = LinearMap.id := by
  exact Module.Projective.lift (LinearMap.id) q hq

end

end ProjectiveSurjectionSplitAtomic
end Experimental
end PCRLean
