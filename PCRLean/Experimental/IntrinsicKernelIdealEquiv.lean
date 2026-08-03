import Mathlib
import PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient

/-!
# Experimental equivariance of intrinsic kernel ideals

A geometric centre extracted from a conormal quotient must not depend on the
chosen frame of the ambient module. A linear equivalence of source modules
induces an algebra equivalence of their symmetric algebras. If two linear
quotient maps commute with that source equivalence, the induced algebra
equivalence maps the intrinsic kernel ideal of the first map exactly onto the
intrinsic kernel ideal of the second.

Thus the actual centre ideal

`span { SymmetricAlgebra.ι v | v ∈ ker project }`

is presentation invariant under arbitrary linear changes of frame, not merely
under coordinate permutations. This is the overlap theorem needed by the
Fitting-local U2 atlas. Scheme-level localization and effective sheaf descent
remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealEquiv

noncomputable section

universe u v v' w

variable {R : Type u} [CommRing R]
variable {V : Type v} {V' : Type v'} {Kmod : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup V'] [Module R V']
variable [AddCommGroup Kmod] [Module R Kmod]

open SurjectiveLinearMapSymmetricQuotient

/-- Algebra map on symmetric algebras induced by a linear equivalence. -/
def symmetricAlgHom (e : V ≃ₗ[R] V') :
    SymmetricAlgebra R V →ₐ[R] SymmetricAlgebra R V' :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R V').comp e.toLinearMap)

@[simp] theorem symmetricAlgHom_ι
    (e : V ≃ₗ[R] V') (v : V) :
    symmetricAlgHom e (SymmetricAlgebra.ι R V v) =
      SymmetricAlgebra.ι R V' (e v) := by
  simp [symmetricAlgHom]

/-- The map induced by the inverse linear equivalence is a left inverse. -/
theorem symmetricAlgHom_symm_comp
    (e : V ≃ₗ[R] V') :
    (symmetricAlgHom e.symm).comp (symmetricAlgHom e) =
      AlgHom.id R (SymmetricAlgebra R V) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

/-- The map induced by the inverse linear equivalence is a right inverse. -/
theorem symmetricAlgHom_comp_symm
    (e : V ≃ₗ[R] V') :
    (symmetricAlgHom e).comp (symmetricAlgHom e.symm) =
      AlgHom.id R (SymmetricAlgebra R V') := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

/-- Linear changes of frame induce algebra equivalences of symmetric algebras. -/
noncomputable def symmetricAlgEquiv (e : V ≃ₗ[R] V') :
    SymmetricAlgebra R V ≃ₐ[R] SymmetricAlgebra R V' :=
  AlgEquiv.ofAlgHom
    (symmetricAlgHom e)
    (symmetricAlgHom e.symm)
    (symmetricAlgHom_comp_symm e)
    (symmetricAlgHom_symm_comp e)

@[simp] theorem symmetricAlgEquiv_ι
    (e : V ≃ₗ[R] V') (v : V) :
    symmetricAlgEquiv e (SymmetricAlgebra.ι R V v) =
      SymmetricAlgebra.ι R V' (e v) := by
  simp [symmetricAlgEquiv]

variable
    (project : V →ₗ[R] Kmod)
    (project' : V' →ₗ[R] Kmod)
    (e : V ≃ₗ[R] V')

/-- Compatibility square for two presentations of the same quotient map. -/
def Compatible : Prop :=
  project'.comp e.toLinearMap = project

/-- A compatible frame change sends kernel vectors to kernel vectors. -/
theorem map_mem_ker
    (hcompat : Compatible project project' e)
    {v : V} (hv : v ∈ project.ker) :
    e v ∈ project'.ker := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun hcompat v
  have hv0 : project v = 0 := LinearMap.mem_ker.mp hv
  simpa [Compatible, LinearMap.comp_apply, hv0] using h

/-- The inverse frame change sends kernel vectors back to kernel vectors. -/
theorem symm_mem_ker
    (hcompat : Compatible project project' e)
    {v' : V'} (hv' : v' ∈ project'.ker) :
    e.symm v' ∈ project.ker := by
  apply LinearMap.mem_ker.mpr
  have h := LinearMap.congr_fun hcompat (e.symm v')
  have hv0 : project' v' = 0 := LinearMap.mem_ker.mp hv'
  simpa [Compatible, LinearMap.comp_apply, hv0] using h.symm

/-- Main overlap theorem: compatible linear frames define exactly the same
actual centre ideal after transport by the induced symmetric-algebra
equivalence. -/
theorem map_kernelIdeal_eq
    (hcompat : Compatible project project' e) :
    Ideal.map (symmetricAlgEquiv e).toAlgHom.toRingHom
        (kernelIdeal project) =
      kernelIdeal project' := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, kernelIdeal, Ideal.span_le]
    rintro x ⟨k, rfl⟩
    rw [Ideal.mem_comap]
    rw [symmetricAlgEquiv_ι]
    apply Ideal.subset_span
    exact ⟨⟨e k.1, map_mem_ker project project' e hcompat k.2⟩, rfl⟩
  · rw [kernelIdeal, Ideal.span_le]
    rintro x ⟨k, rfl⟩
    have hk : e.symm k.1 ∈ project.ker :=
      symm_mem_ker project project' e hcompat k.2
    have hgen :
        SymmetricAlgebra.ι R V (e.symm k.1) ∈
          kernelIdeal project :=
      Ideal.subset_span ⟨⟨e.symm k.1, hk⟩, rfl⟩
    have hm := Ideal.mem_map_of_mem
      (symmetricAlgEquiv e).toAlgHom.toRingHom hgen
    simpa using hm

/-- Surjectivity of the quotient map is invariant under a compatible source
frame change. -/
theorem surjective_iff
    (hcompat : Compatible project project' e) :
    Function.Surjective project ↔ Function.Surjective project' := by
  constructor
  · intro h y
    rcases h y with ⟨v, hv⟩
    refine ⟨e v, ?_⟩
    have hc := LinearMap.congr_fun hcompat v
    simpa [Compatible, LinearMap.comp_apply, hv] using hc
  · intro h y
    rcases h y with ⟨v', hv'⟩
    refine ⟨e.symm v', ?_⟩
    have hc := LinearMap.congr_fun hcompat (e.symm v')
    simpa [Compatible, LinearMap.comp_apply, hv'] using hc.symm

end

end IntrinsicKernelIdealEquiv
end Experimental
end PCRLean
