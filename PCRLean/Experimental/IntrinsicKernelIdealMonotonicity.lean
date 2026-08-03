import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality

/-!
# Experimental monotonicity of intrinsic kernel ideals

The intrinsic symmetric-algebra centre ideal is monotone in the linear kernel:
a larger kernel generates a larger actual ideal.  Postcomposing a packet map
can only enlarge its kernel and therefore its centre ideal; injective
postcomposition leaves both unchanged.

These order laws are the algebraic basis for Fitting-rank centre words.  They do
not assert that strict kernel growth gives strict ideal growth over an arbitrary
base, nor that geometric blowup transforms realize these order relations.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealMonotonicity

noncomputable section

universe u v w w'

variable {R : Type u} [CommRing R]
variable {V : Type v} {Kmod : Type w} {Kmod' : Type w'}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup Kmod] [Module R Kmod]
variable [AddCommGroup Kmod'] [Module R Kmod']

open IntrinsicKernelIdealFunctoriality

/-- Kernel inclusion gives inclusion of the generated actual centre ideals. -/
theorem kernelIdealOf_mono
    {project : V →ₗ[R] Kmod} {project' : V →ₗ[R] Kmod'}
    (hker : project.ker ≤ project'.ker) :
    kernelIdealOf project ≤ kernelIdealOf project' := by
  rw [kernelIdealOf, Ideal.span_le]
  rintro x ⟨k, rfl⟩
  apply Ideal.subset_span
  exact ⟨⟨k.1, hker k.2⟩, rfl⟩

/-- Postcomposition can only enlarge the kernel ideal. -/
theorem kernelIdealOf_le_comp
    (project : V →ₗ[R] Kmod) (g : Kmod →ₗ[R] Kmod') :
    kernelIdealOf project ≤ kernelIdealOf (g.comp project) := by
  apply kernelIdealOf_mono
  intro x hx
  apply LinearMap.mem_ker.mpr
  have hzero : project x = 0 := LinearMap.mem_ker.mp hx
  simp [LinearMap.comp_apply, hzero]

/-- Injective postcomposition preserves the linear kernel. -/
theorem ker_comp_eq_of_injective
    (project : V →ₗ[R] Kmod) (g : Kmod →ₗ[R] Kmod')
    (hg : Function.Injective g) :
    (g.comp project).ker = project.ker := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply hg
    have hzero : g (project x) = 0 := LinearMap.mem_ker.mp hx
    simpa using hzero
  · intro hx
    apply LinearMap.mem_ker.mpr
    have hzero : project x = 0 := LinearMap.mem_ker.mp hx
    simp [LinearMap.comp_apply, hzero]

/-- Injective postcomposition preserves the intrinsic actual centre exactly. -/
theorem kernelIdealOf_comp_eq_of_injective
    (project : V →ₗ[R] Kmod) (g : Kmod →ₗ[R] Kmod')
    (hg : Function.Injective g) :
    kernelIdealOf (g.comp project) = kernelIdealOf project :=
  kernelIdealOf_eq_of_ker_eq (g.comp project) project
    (ker_comp_eq_of_injective project g hg)

end

end IntrinsicKernelIdealMonotonicity
end Experimental
end PCRLean
