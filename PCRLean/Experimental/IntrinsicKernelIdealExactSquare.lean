import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality

/-!
# Experimental exact-square transport for intrinsic kernel ideals

A commuting square gives forward containment of intrinsic kernel ideals.  Exact
transport requires one additional condition: every vector in the new kernel is
the image of a vector in the old kernel.  Under this kernel-surjectivity
condition, the induced symmetric-algebra map carries the old actual centre
ideal exactly onto the new one.

Kernel-exact squares admit identities and composition.  They therefore form a
composable hereditary transport certificate for chart changes, localizations,
flat base changes, or blowup transforms once the geometric layer proves the
kernel-surjectivity condition.  This file does not prove that arbitrary
geometric transforms supply such a square.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelIdealExactSquare

noncomputable section

universe u v₀ v₁ v₂ w₀ w₁ w₂

variable {R : Type u} [CommRing R]

open IntrinsicKernelIdealFunctoriality

/-- A commuting square which is surjective on the relevant linear kernels. -/
structure KernelExactSquare
    {V₀ : Type v₀} {V₁ : Type v₁}
    {K₀ : Type w₀} {K₁ : Type w₁}
    [AddCommGroup V₀] [Module R V₀]
    [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup K₁] [Module R K₁]
    (project₀ : V₀ →ₗ[R] K₀) (project₁ : V₁ →ₗ[R] K₁) where
  sourceMap : V₀ →ₗ[R] V₁
  targetMap : K₀ →ₗ[R] K₁
  commutes : project₁.comp sourceMap = targetMap.comp project₀
  kernel_surjective : ∀ k₁ : project₁.ker,
    ∃ k₀ : project₀.ker, sourceMap k₀.1 = k₁.1

namespace KernelExactSquare

variable
    {V₀ : Type v₀} {V₁ : Type v₁} {V₂ : Type v₂}
    {K₀ : Type w₀} {K₁ : Type w₁} {K₂ : Type w₂}
    [AddCommGroup V₀] [Module R V₀]
    [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup V₂] [Module R V₂]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₂] [Module R K₂]
    {project₀ : V₀ →ₗ[R] K₀}
    {project₁ : V₁ →ₗ[R] K₁}
    {project₂ : V₂ →ₗ[R] K₂}

/-- A kernel-exact square transports the intrinsic actual centre exactly. -/
theorem map_kernelIdealOf_eq
    (E : KernelExactSquare project₀ project₁) :
    Ideal.map (symmetricMap E.sourceMap) (kernelIdealOf project₀) =
      kernelIdealOf project₁ := by
  apply le_antisymm
  · exact map_kernelIdealOf_le project₀ project₁
      E.sourceMap E.targetMap E.commutes
  · rw [kernelIdealOf, Ideal.span_le]
    rintro x ⟨k₁, rfl⟩
    rcases E.kernel_surjective k₁ with ⟨k₀, hk⟩
    have hgen : SymmetricAlgebra.ι R V₀ k₀.1 ∈
        kernelIdealOf project₀ := by
      apply Ideal.subset_span
      exact ⟨k₀, rfl⟩
    have hmapped := Ideal.mem_map_of_mem (symmetricMap E.sourceMap) hgen
    simpa [symmetricMap_ι, hk] using hmapped

/-- Identity kernel-exact square. -/
def refl (project₀ : V₀ →ₗ[R] K₀) :
    KernelExactSquare project₀ project₀ where
  sourceMap := LinearMap.id
  targetMap := LinearMap.id
  commutes := by ext x <;> rfl
  kernel_surjective := by
    intro k
    exact ⟨k, rfl⟩

/-- Composition of kernel-exact squares. -/
def comp
    (E₀₁ : KernelExactSquare project₀ project₁)
    (E₁₂ : KernelExactSquare project₁ project₂) :
    KernelExactSquare project₀ project₂ where
  sourceMap := E₁₂.sourceMap.comp E₀₁.sourceMap
  targetMap := E₁₂.targetMap.comp E₀₁.targetMap
  commutes := by
    ext x
    have h₀₁ := LinearMap.congr_fun E₀₁.commutes x
    have h₁₂ := LinearMap.congr_fun E₁₂.commutes (E₀₁.sourceMap x)
    simpa [LinearMap.comp_apply, h₀₁] using h₁₂
  kernel_surjective := by
    intro k₂
    rcases E₁₂.kernel_surjective k₂ with ⟨k₁, hk₁⟩
    rcases E₀₁.kernel_surjective k₁ with ⟨k₀, hk₀⟩
    refine ⟨k₀, ?_⟩
    simp [LinearMap.comp_apply, hk₀, hk₁]

/-- Exact transport along a composite is the expected two-stage ideal
transport. -/
theorem map_kernelIdealOf_eq_comp
    (E₀₁ : KernelExactSquare project₀ project₁)
    (E₁₂ : KernelExactSquare project₁ project₂) :
    Ideal.map (symmetricMap (E₁₂.sourceMap.comp E₀₁.sourceMap))
        (kernelIdealOf project₀) = kernelIdealOf project₂ :=
  (E₀₁.comp E₁₂).map_kernelIdealOf_eq

end KernelExactSquare

end

end IntrinsicKernelIdealExactSquare
end Experimental
end PCRLean
