import Mathlib

/-!
# Split linear kernels as regular centre models

A constant-rank differential packet gives a linear map from a conormal space to
its coefficient space. If the map has a linear right inverse, its kernel is an
actual split linear subspace. This file constructs the explicit product
decomposition. In geometry, a locally split map of vector bundles cuts out a
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

/-- A linear surjection equipped with a chosen right inverse. -/
structure SplitMap where
  map : V →ₗ[K] W
  rightInv : W →ₗ[K] V
  rightInv_spec : map.comp rightInv = LinearMap.id

namespace SplitMap

variable (S : SplitMap (K := K) (V := V) (W := W))

@[simp] theorem map_rightInv (w : W) : S.map (S.rightInv w) = w := by
  have h := LinearMap.congr_fun S.rightInv_spec w
  simpa using h

/-- Projection of a vector to the kernel component. -/
def kernelPart (v : V) : V := v - S.rightInv (S.map v)

@[simp] theorem map_kernelPart (v : V) : S.map (S.kernelPart v) = 0 := by
  simp [kernelPart]

@[simp] theorem kernelPart_add (x y : V) :
    S.kernelPart (x + y) = S.kernelPart x + S.kernelPart y := by
  simp [kernelPart]
  abel

@[simp] theorem kernelPart_smul (a : K) (x : V) :
    S.kernelPart (a • x) = a • S.kernelPart x := by
  simp [kernelPart, smul_sub]

/-- Kernel component as an element of the kernel subtype. -/
def kernelPartSubtype (v : V) : LinearMap.ker S.map :=
  ⟨S.kernelPart v, S.map_kernelPart v⟩

/-- Coordinates in the product `ker(map) × W`. -/
def toProd : V →ₗ[K] (LinearMap.ker S.map × W) where
  toFun v := (S.kernelPartSubtype v, S.map v)
  map_add' x y := by
    apply Prod.ext
    · ext
      exact S.kernelPart_add x y
    · exact S.map.map_add x y
  map_smul' a x := by
    apply Prod.ext
    · ext
      exact S.kernelPart_smul a x
    · exact S.map.map_smul a x

/-- Reconstruct a vector from its kernel and transverse components. -/
def fromProd : (LinearMap.ker S.map × W) →ₗ[K] V where
  toFun z := (z.1 : V) + S.rightInv z.2
  map_add' x y := by
    dsimp
    rw [map_add]
    abel
  map_smul' a x := by
    dsimp
    rw [map_smul]
    exact smul_add a (x.1 : V) (S.rightInv x.2)

@[simp] theorem fromProd_toProd (v : V) :
    S.fromProd (S.toProd v) = v := by
  simp [fromProd, toProd, kernelPartSubtype, kernelPart]

@[simp] theorem toProd_fromProd (z : LinearMap.ker S.map × W) :
    S.toProd (S.fromProd z) = z := by
  rcases z with ⟨k, w⟩
  apply Prod.ext
  · ext
    simp [fromProd, toProd, kernelPartSubtype, kernelPart]
  · simp [fromProd, toProd]

/-- Explicit product decomposition of a split linear packet. -/
def equivKernelProd : V ≃ₗ[K] (LinearMap.ker S.map × W) where
  toLinearMap := S.toProd
  invFun := S.fromProd
  left_inv := S.fromProd_toProd
  right_inv := S.toProd_fromProd

/-- The right inverse is injective. -/
theorem rightInv_injective : Function.Injective S.rightInv := by
  intro x y hxy
  have h := congrArg S.map hxy
  simpa using h

/-- The kernel and the image of the right inverse meet only in zero. -/
theorem ker_disjoint_range_rightInv :
    Disjoint (LinearMap.ker S.map) (LinearMap.range S.rightInv) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rcases hx with ⟨hxker, hxrange⟩
  rcases hxrange with ⟨w, rfl⟩
  have hw : w = 0 := by
    have hm : S.map (S.rightInv w) = 0 := hxker
    simpa using hm
  subst w
  simp

/-- The kernel and right-inverse image span the whole source. -/
theorem ker_sup_range_rightInv :
    LinearMap.ker S.map ⊔ LinearMap.range S.rightInv = ⊤ := by
  apply top_unique
  intro v hv
  have hk : S.kernelPart v ∈ LinearMap.ker S.map := S.map_kernelPart v
  have hs : S.rightInv (S.map v) ∈ LinearMap.range S.rightInv :=
    ⟨S.map v, rfl⟩
  have hsum : S.kernelPart v + S.rightInv (S.map v) ∈
      LinearMap.ker S.map ⊔ LinearMap.range S.rightInv :=
    Submodule.add_mem_sup hk hs
  simpa [kernelPart] using hsum

/-- The kernel and chosen transverse image are complementary. -/
theorem isCompl_kernel_range_rightInv :
    IsCompl (LinearMap.ker S.map) (LinearMap.range S.rightInv) :=
  ⟨S.ker_disjoint_range_rightInv,
    codisjoint_iff.mpr S.ker_sup_range_rightInv⟩

end SplitMap

end

end SplitKernelCentre
end PCRLean
