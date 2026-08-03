import Mathlib
import PCRLean.Experimental.SplitRetractionBoundaryQuotient
import PCRLean.Experimental.BoundaryTransversalityGate

/-!
# Transversality for split retraction kernels

Let `p : A → B` admit a ring section `s`.  Put `K = ker(p)` and let `J ⊂ B`.
The extension of `J` to `A` is `J.map s`.  The additive decomposition

`a = s(p(a)) + (a - s(p(a)))`

shows that

`K ⊓ J.map s = K * J.map s`.

Thus the retraction kernel is ideal-theoretically transverse to every boundary
ideal pulled back from the retract.  For polynomial graph centres this proves
the first-order no-overlap part of boundary SNC for all coefficient-ring
strata, not only coordinate strata.

The proof is constructive.  It builds an auxiliary ideal consisting of elements
whose projection lies in `J` and whose residual belongs to the mixed product.
The mapped boundary ideal lies in this auxiliary ideal; restricting to the
kernel identifies the residual with the original element.
-/

namespace PCRLean
namespace Experimental
namespace SplitRetractionTransversality

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

open SplitRetractionBoundaryQuotient
open BoundaryTransversalityGate

variable (S : Retraction (A := A) (B := B))

/-- Residual from the chosen section. -/
def residual (a : A) : A :=
  a - S.section (S.project a)

/-- Every residual lies in the retraction kernel. -/
theorem residual_mem_kernel (a : A) :
    S.residual a ∈ RingHom.ker S.project := by
  apply RingHom.mem_ker.mpr
  simp [residual]

/-- Residual of a section element vanishes. -/
@[simp] theorem residual_section (b : B) :
    S.residual (S.section b) = 0 := by
  simp [residual]

/-- Product rule for the residual projection. -/
theorem residual_mul (a x : A) :
    S.residual (a * x) =
      a * S.residual x +
        S.residual a * S.section (S.project x) := by
  simp [residual, map_mul]
  ring

/-- Auxiliary ideal implementing the split decomposition relative to `J`. -/
def decompositionIdeal (J : Ideal B) : Ideal A where
  carrier := {x | S.project x ∈ J ∧
    S.residual x ∈ RingHom.ker S.project * J.map S.section}
  zero_mem' := by simp [residual]
  add_mem' := by
    intro x y hx hy
    constructor
    · simpa using J.add_mem hx.1 hy.1
    · have hr : S.residual (x + y) = S.residual x + S.residual y := by
        simp [residual]
      rw [hr]
      exact (RingHom.ker S.project * J.map S.section).add_mem hx.2 hy.2
  smul_mem' := by
    intro a x hx
    constructor
    · simpa using J.mul_mem_left (S.project a) hx.1
    · rw [smul_eq_mul, S.residual_mul]
      apply (RingHom.ker S.project * J.map S.section).add_mem
      · exact (RingHom.ker S.project * J.map S.section).mul_mem_left a hx.2
      · exact Ideal.mul_mem_mul
          (S.residual_mem_kernel a)
          (Ideal.mem_map_of_mem S.section hx.1)

/-- The extended boundary ideal lies in the decomposition ideal. -/
theorem map_le_decompositionIdeal (J : Ideal B) :
    J.map S.section ≤ S.decompositionIdeal J := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap]
  constructor
  · simpa using hb
  · simp [residual]

/-- Main transversality theorem for split retractions. -/
theorem kernel_transverse_mappedIdeal (J : Ideal B) :
    Transverse (RingHom.ker S.project) (J.map S.section) := by
  unfold Transverse
  apply le_antisymm
  · intro x hx
    have hdec : x ∈ S.decompositionIdeal J :=
      S.map_le_decompositionIdeal J hx.2
    have hp : S.project x = 0 := RingHom.mem_ker.mp hx.1
    have hres := hdec.2
    simpa [residual, hp] using hres
  · exact le_inf (by
      rw [mul_comm]
      exact Ideal.mul_le_left) Ideal.mul_le_left

end

end SplitRetractionTransversality
end Experimental
end PCRLean
