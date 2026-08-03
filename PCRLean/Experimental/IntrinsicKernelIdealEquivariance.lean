import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality

/-!
# Experimental intrinsic kernel-ideal equivariance

If a pair of linear equivalences identifies two quotient maps by a commuting
square, the induced symmetric-algebra coordinate change carries the intrinsic
kernel ideal exactly onto the new intrinsic kernel ideal. Thus the actual
centre is invariant under invertible changes of source and target frames.

This is an affine overlap theorem. It does not construct the transition linear
equivalences from arbitrary geometric charts and does not address localization,
saturation, or nonlinear strict transforms.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealEquivariance

noncomputable section

universe u v v' w w'

variable {R : Type u} [CommRing R]
variable {V : Type v} {V' : Type v'}
variable {Kmod : Type w} {Kmod' : Type w'}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup V'] [Module R V']
variable [AddCommGroup Kmod] [Module R Kmod]
variable [AddCommGroup Kmod'] [Module R Kmod']

open IntrinsicKernelIdealFunctoriality

/-- Exact transport of the intrinsic actual centre under a commuting pair of
linear equivalences. -/
theorem map_kernelIdealOf_eq_of_equiv
    (project : V →ₗ[R] Kmod)
    (project' : V' →ₗ[R] Kmod')
    (eV : V ≃ₗ[R] V')
    (eK : Kmod ≃ₗ[R] Kmod')
    (hcomm : project'.comp eV.toLinearMap =
      eK.toLinearMap.comp project) :
    Ideal.map (symmetricMap eV.toLinearMap) (kernelIdealOf project) =
      kernelIdealOf project' := by
  apply le_antisymm
  · exact map_kernelIdealOf_le
      project project' eV.toLinearMap eK.toLinearMap hcomm
  · rw [kernelIdealOf, Ideal.span_le]
    rintro x ⟨k, rfl⟩
    have hkSource : project (eV.symm k.1) = 0 := by
      apply eK.injective
      have hkTarget : project' k.1 = 0 := LinearMap.mem_ker.mp k.2
      have hpoint := LinearMap.congr_fun hcomm (eV.symm k.1)
      simpa [LinearMap.comp_apply, hkTarget] using hpoint.symm
    have hgen :
        SymmetricAlgebra.ι R V (eV.symm k.1) ∈
          kernelIdealOf project := by
      apply Ideal.subset_span
      exact ⟨⟨eV.symm k.1, LinearMap.mem_ker.mpr hkSource⟩, rfl⟩
    have hmapped := Ideal.mem_map_of_mem
      (symmetricMap eV.toLinearMap) hgen
    simpa using hmapped

/-- Split-surjection form of the same exact overlap theorem. -/
theorem map_splitSurjection_kernelIdeal_eq_of_equiv
    (S : SplitSurjectionSymmetricQuotient.SplitSurjection
      (R := R) (V := V) (Kmod := Kmod))
    (T : SplitSurjectionSymmetricQuotient.SplitSurjection
      (R := R) (V := V') (Kmod := Kmod'))
    (eV : V ≃ₗ[R] V')
    (eK : Kmod ≃ₗ[R] Kmod')
    (hcomm : T.project.comp eV.toLinearMap =
      eK.toLinearMap.comp S.project) :
    Ideal.map (symmetricMap eV.toLinearMap) S.kernelIdeal =
      T.kernelIdeal := by
  simpa [splitSurjection_kernelIdeal_eq] using
    map_kernelIdealOf_eq_of_equiv S.project T.project eV eK hcomm

end

end IntrinsicKernelIdealEquivariance
end Experimental
end PCRLean
