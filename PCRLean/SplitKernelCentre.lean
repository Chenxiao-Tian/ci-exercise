import Mathlib

/-!
# Split linear kernels as regular centre models

A constant-rank differential packet gives a linear map from a conormal space to
its coefficient space.  If the map has a linear section, its kernel is an
actual split linear subspace.  This file constructs the explicit product
decomposition.  In geometry, a locally split map of vector bundles cuts out a
regular linear centre; the sheaf and scheme descent are separate obligations.
-/

namespace PCRLean
namespace SplitKernelCentre

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A linear surjection equipped with a chosen section. -/
structure SplitMap where
  map : V →ₗ[K] W
  section : W →ₗ[K] V
  rightInverse : map.comp section = LinearMap.id

namespace SplitMap

variable (S : SplitMap (K := K) (V := V) (W := W))

@[simp] theorem map_section (w : W) : S.map (S.section w) = w := by
  have h := LinearMap.congr_fun S.rightInverse w
  simpa using h

/-- Projection of a vector to the kernel component. -/
def kernelPart (v : V) : V := v - S.section (S.map v)

@[simp] theorem map_kernelPart (v : V) : S.map (S.kernelPart v) = 0 := by
  simp [kernelPart, map_section]

/-- Kernel component as an element of the kernel subtype. -/
def kernelPartSubtype (v : V) : LinearMap.ker S.map :=
  ⟨S.kernelPart v, S.map_kernelPart v⟩

/-- Coordinates in the product `ker(map) × W`. -/
def toProd : V →ₗ[K] (LinearMap.ker S.map × W) where
  toFun v := (S.kernelPartSubtype v, S.map v)
  map_add' x y := by
    apply Prod.ext
    · ext
      simp [kernelPartSubtype, kernelPart]
    · simp
  map_smul' a x := by
    apply Prod.ext
    · ext
      simp [kernelPartSubtype, kernelPart]
    · simp

/-- Reconstruct a vector from its kernel and transverse components. -/
def fromProd : (LinearMap.ker S.map × W) →ₗ[K] V where
  toFun z := (z.1 : V) + S.section z.2
  map_add' x y := by
    simp
    abel
  map_smul' a x := by
    simp [smul_add]

@[simp] theorem fromProd_toProd (v : V) :
    S.fromProd (S.toProd v) = v := by
  simp [fromProd, toProd, kernelPartSubtype, kernelPart]

@[simp] theorem toProd_fromProd (z : LinearMap.ker S.map × W) :
    S.toProd (S.fromProd z) = z := by
  rcases z with ⟨k, w⟩
  apply Prod.ext
  · ext
    simp [fromProd, toProd, kernelPartSubtype, kernelPart, map_section]
  · simp [fromProd, toProd, map_section]

/-- Explicit product decomposition of a split linear packet. -/
def equivKernelProd : V ≃ₗ[K] (LinearMap.ker S.map × W) where
  toLinearMap := S.toProd
  invFun := S.fromProd
  left_inv := S.fromProd_toProd
  right_inv := S.toProd_fromProd

/-- The section is injective. -/
theorem section_injective : Function.Injective S.section := by
  intro x y hxy
  apply S.map_section x ▸ S.map_section y ▸ congrArg S.map hxy

/-- The kernel and the image of the section meet only in zero. -/
theorem ker_disjoint_range_section :
    Disjoint (LinearMap.ker S.map) (LinearMap.range S.section) := by
  rw [Submodule.disjoint_left]
  intro x hxker hxrange
  rcases hxrange with ⟨w, rfl⟩
  have hm : S.map (S.section w) = 0 := hxker
  rw [S.map_section] at hm
  subst w
  simp

/-- The kernel and section image span the whole source. -/
theorem ker_sup_range_section :
    LinearMap.ker S.map ⊔ LinearMap.range S.section = ⊤ := by
  apply top_unique
  intro v hv
  have hk : S.kernelPart v ∈ LinearMap.ker S.map := S.map_kernelPart v
  have hs : S.section (S.map v) ∈ LinearMap.range S.section :=
    ⟨S.map v, rfl⟩
  have hsum : S.kernelPart v + S.section (S.map v) ∈
      LinearMap.ker S.map ⊔ LinearMap.range S.section :=
    (Submodule.add_mem_sup hk hs)
  simpa [kernelPart] using hsum

/-- The kernel and chosen transverse image are complementary. -/
theorem isCompl_kernel_range_section :
    IsCompl (LinearMap.ker S.map) (LinearMap.range S.section) :=
  ⟨S.ker_disjoint_range_section, codisjoint_iff.mpr S.ker_sup_range_section⟩

end SplitMap

end

end SplitKernelCentre
end PCRLean
