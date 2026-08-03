import Mathlib
import PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient

/-!
# Experimental composition law for intrinsic kernel ideals

A chain of conormal quotient maps gives a canonical nested chain of actual
centre ideals. If `project : V → K` and `next : K → L`, then every vector killed
by `project` is killed by `next ∘ project`, so the intrinsic ideal of the first
quotient is contained in the intrinsic ideal of the composite. If the second
map is injective, no new kernel directions appear and the two centre ideals are
equal.

This gives the algebraic order relation needed for a finite Fitting centre
word: passing to a smaller quotient enlarges the actual centre, while an
invertible row change leaves it unchanged.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealComposition

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {V : Type v} {Kmod : Type w} {Lmod : Type x}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup Kmod] [Module R Kmod]
variable [AddCommGroup Lmod] [Module R Lmod]

open SurjectiveLinearMapSymmetricQuotient

/-- Kernels are monotone under postcomposition. -/
theorem ker_le_ker_comp
    (project : V →ₗ[R] Kmod) (next : Kmod →ₗ[R] Lmod) :
    project.ker ≤ (next.comp project).ker := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  have hv0 : project v = 0 := LinearMap.mem_ker.mp hv
  simp [LinearMap.comp_apply, hv0]

/-- Postcomposition can only enlarge the intrinsic actual centre ideal. -/
theorem kernelIdeal_le_comp
    (project : V →ₗ[R] Kmod) (next : Kmod →ₗ[R] Lmod) :
    kernelIdeal project ≤ kernelIdeal (next.comp project) := by
  rw [kernelIdeal, kernelIdeal, Ideal.span_le]
  rintro z ⟨k, rfl⟩
  apply Ideal.subset_span
  exact ⟨⟨k.1, ker_le_ker_comp project next k.2⟩, rfl⟩

/-- An injective postcomposition creates no new kernel directions. -/
theorem ker_comp_eq_of_injective
    (project : V →ₗ[R] Kmod) (next : Kmod →ₗ[R] Lmod)
    (hnext : Function.Injective next) :
    (next.comp project).ker = project.ker := by
  apply le_antisymm
  · intro v hv
    apply LinearMap.mem_ker.mpr
    have hzero : next (project v) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.mem_ker.mp hv
    exact hnext (by simpa using hzero)
  · exact ker_le_ker_comp project next

/-- Consequently an injective row change leaves the actual centre ideal
unchanged. -/
theorem kernelIdeal_comp_eq_of_injective
    (project : V →ₗ[R] Kmod) (next : Kmod →ₗ[R] Lmod)
    (hnext : Function.Injective next) :
    kernelIdeal (next.comp project) = kernelIdeal project := by
  apply le_antisymm
  · rw [kernelIdeal, Ideal.span_le]
    rintro z ⟨k, rfl⟩
    have hk : k.1 ∈ project.ker := by
      apply LinearMap.mem_ker.mpr
      have hzero : next (project k.1) = 0 := by
        simpa [LinearMap.comp_apply] using LinearMap.mem_ker.mp k.2
      exact hnext (by simpa using hzero)
    exact Ideal.subset_span ⟨⟨k.1, hk⟩, rfl⟩
  · exact kernelIdeal_le_comp project next

/-- In particular a target linear equivalence does not change the intrinsic
centre ideal. -/
theorem kernelIdeal_comp_equiv
    (project : V →ₗ[R] Kmod) (next : Kmod ≃ₗ[R] Lmod) :
    kernelIdeal (next.toLinearMap.comp project) = kernelIdeal project :=
  kernelIdeal_comp_eq_of_injective project next.toLinearMap next.injective

/-- Surjections compose. -/
theorem surjective_comp
    (project : V →ₗ[R] Kmod) (next : Kmod →ₗ[R] Lmod)
    (hproject : Function.Surjective project)
    (hnext : Function.Surjective next) :
    Function.Surjective (next.comp project) := by
  intro y
  rcases hnext y with ⟨k, hk⟩
  rcases hproject k with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simp [LinearMap.comp_apply, hv, hk]

end

end IntrinsicKernelIdealComposition
end Experimental
end PCRLean
