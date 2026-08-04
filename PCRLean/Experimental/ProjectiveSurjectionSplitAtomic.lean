import Mathlib

/-!
# Projective surjections split

An explicit surjective linear map onto a projective module admits a linear
section. This is the projective half of the X032 finite split-presentation
bridge. Finite generation and construction of a finite-free surjection remain
separate obligations.
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

/-- Every surjection onto a projective module has a linear right inverse. -/
theorem projective_surjection_splits
    (q : F →ₗ[R] P) (hq : Function.Surjective q) :
    ∃ s : P →ₗ[R] F, q.comp s = LinearMap.id := by
  exact Module.Projective.lift (LinearMap.id) q hq

end

end ProjectiveSurjectionSplitAtomic
end Experimental
end PCRLean
