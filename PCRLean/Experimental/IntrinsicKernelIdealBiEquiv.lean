import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealEquiv

/-!
# Experimental bi-equivariance of intrinsic kernel ideals

Local conormal quotient maps may be written in different frames on both the
ambient module and the quotient module. A commuting square of linear
equivalences preserves the intrinsic actual centre ideal. The target
equivalence identifies quotient presentations; the transported centre is
controlled by the source equivalence.

This removes both source-frame and packet-row-frame choices from the affine U2
construction. Effective localization and sheaf descent are still geometric
obligations.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealBiEquiv

noncomputable section

universe u v v' w w'

variable {R : Type u} [CommRing R]
variable {V : Type v} {V' : Type v'}
variable {Kmod : Type w} {Kmod' : Type w'}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup V'] [Module R V']
variable [AddCommGroup Kmod] [Module R Kmod]
variable [AddCommGroup Kmod'] [Module R Kmod']

open SurjectiveLinearMapSymmetricQuotient
open IntrinsicKernelIdealEquiv

variable
    (project : V →ₗ[R] Kmod)
    (project' : V' →ₗ[R] Kmod')
    (source : V ≃ₗ[R] V')
    (target : Kmod ≃ₗ[R] Kmod')

/-- Commuting square for two source-and-target presentations. -/
def Compatible : Prop :=
  project'.comp source.toLinearMap =
    target.toLinearMap.comp project

/-- The source equivalence maps the first linear kernel into the second. -/
theorem map_mem_ker
    (hcompat : Compatible project project' source target)
    {v : V} (hv : v ∈ project.ker) :
    source v ∈ project'.ker := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun hcompat v
  have hv0 : project v = 0 := LinearMap.mem_ker.mp hv
  simpa [Compatible, LinearMap.comp_apply, hv0] using h

/-- The inverse source equivalence maps the second kernel back into the first. -/
theorem symm_mem_ker
    (hcompat : Compatible project project' source target)
    {v' : V'} (hv' : v' ∈ project'.ker) :
    source.symm v' ∈ project.ker := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun hcompat (source.symm v')
  have hv0 : project' v' = 0 := LinearMap.mem_ker.mp hv'
  have ht : target (project (source.symm v')) = 0 := by
    simpa [Compatible, LinearMap.comp_apply, hv0] using h.symm
  apply target.injective
  simpa using ht

/-- Main source-and-target frame-independence theorem for the actual centre. -/
theorem map_kernelIdeal_eq
    (hcompat : Compatible project project' source target) :
    Ideal.map (symmetricAlgEquiv source).toAlgHom.toRingHom
        (kernelIdeal project) =
      kernelIdeal project' := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, kernelIdeal, Ideal.span_le]
    rintro x ⟨k, rfl⟩
    rw [Ideal.mem_comap]
    rw [symmetricAlgEquiv_ι]
    apply Ideal.subset_span
    exact ⟨⟨source k.1,
      map_mem_ker project project' source target hcompat k.2⟩, rfl⟩
  · rw [kernelIdeal, Ideal.span_le]
    rintro x ⟨k, rfl⟩
    have hk : source.symm k.1 ∈ project.ker :=
      symm_mem_ker project project' source target hcompat k.2
    have hgen :
        SymmetricAlgebra.ι R V (source.symm k.1) ∈
          kernelIdeal project :=
      Ideal.subset_span ⟨⟨source.symm k.1, hk⟩, rfl⟩
    have hm := Ideal.mem_map_of_mem
      (symmetricAlgEquiv source).toAlgHom.toRingHom hgen
    simpa using hm

/-- Surjectivity is invariant under simultaneous source and target frame
changes. -/
theorem surjective_iff
    (hcompat : Compatible project project' source target) :
    Function.Surjective project ↔ Function.Surjective project' := by
  constructor
  · intro h y'
    rcases h (target.symm y') with ⟨v, hv⟩
    refine ⟨source v, ?_⟩
    have hc := LinearMap.congr_fun hcompat v
    simpa [Compatible, LinearMap.comp_apply, hv] using hc
  · intro h y
    rcases h (target y) with ⟨v', hv'⟩
    refine ⟨source.symm v', ?_⟩
    apply target.injective
    have hc := LinearMap.congr_fun hcompat (source.symm v')
    simpa [Compatible, LinearMap.comp_apply, hv'] using hc.symm

end

end IntrinsicKernelIdealBiEquiv
end Experimental
end PCRLean
