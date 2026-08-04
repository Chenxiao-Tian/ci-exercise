import Mathlib
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# Intrinsic order ideals are invariant under linear equivalence

The order ideal of a section is defined using all linear functionals.  Hence it
is preserved by every linear equivalence, without a chosen basis, dual frame,
or split presentation.  This atomic theorem is the correct overlap firewall
for Fitting-chart cokernel presentations: local frames may change, while the
intrinsic coefficient defect does not.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicOrderIdealLinearEquiv

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} {Q : Type w}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup Q] [Module R Q]

open ProjectiveSectionOrderIdeal

/-- Linear equivalences preserve the intrinsic order ideal exactly. -/
theorem orderIdeal_linearEquiv
    (e : P ≃ₗ[R] Q) (x : P) :
    orderIdeal (e x) = orderIdeal x := by
  apply le_antisymm
  · rw [orderIdeal, Ideal.span_le]
    rintro a ⟨g, rfl⟩
    exact Ideal.subset_span
      ⟨g.comp e.toLinearMap, rfl⟩
  · rw [orderIdeal, Ideal.span_le]
    rintro a ⟨f, rfl⟩
    exact Ideal.subset_span
      ⟨f.comp e.symm.toLinearMap, by simp⟩

/-- Symmetric formulation useful on overlaps. -/
theorem orderIdeal_eq_of_equiv
    (e : P ≃ₗ[R] Q) (x : P) (y : Q)
    (hxy : e x = y) :
    orderIdeal x = orderIdeal y := by
  subst y
  exact (orderIdeal_linearEquiv e x).symm

/-- Zero, proper-nonzero, and unit regimes are consequently invariant under
linear equivalence. -/
theorem regimes_equiv
    (e : P ≃ₗ[R] Q) (x : P) :
    (orderIdeal x = ⊥ ↔ orderIdeal (e x) = ⊥) ∧
    ((orderIdeal x ≠ ⊥ ∧ orderIdeal x ≠ ⊤) ↔
      (orderIdeal (e x) ≠ ⊥ ∧ orderIdeal (e x) ≠ ⊤)) ∧
    (orderIdeal x = ⊤ ↔ orderIdeal (e x) = ⊤) := by
  rw [orderIdeal_linearEquiv e x]

end

end IntrinsicOrderIdealLinearEquiv
end Experimental
end PCRLean
