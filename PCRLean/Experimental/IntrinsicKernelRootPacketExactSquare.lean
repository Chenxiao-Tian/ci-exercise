import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealExactSquare
import PCRLean.Experimental.IntrinsicKernelRootPacket

/-!
# Experimental exact-square transport for intrinsic root packets

A kernel-exact square transports not only the degree-one intrinsic centre ideal
but every intrinsic `q`-th root packet exactly.  Hence one typed geometric
square simultaneously controls the centre and all marked Frobenius-root levels.

This is the hereditary algebraic transport law required by the proposed
centre-word architecture.  It remains conditional on construction of a
kernel-exact square for each actual geometric chart.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicKernelRootPacketExactSquare

noncomputable section

universe u v₀ v₁ w₀ w₁

variable {R : Type u} [CommRing R]
variable {V₀ : Type v₀} {V₁ : Type v₁}
variable {K₀ : Type w₀} {K₁ : Type w₁}
variable [AddCommGroup V₀] [Module R V₀]
variable [AddCommGroup V₁] [Module R V₁]
variable [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup K₁] [Module R K₁]

open IntrinsicKernelIdealFunctoriality
open IntrinsicKernelIdealExactSquare
open IntrinsicKernelRootPacket

variable {project₀ : V₀ →ₗ[R] K₀} {project₁ : V₁ →ₗ[R] K₁}

/-- Exact hereditary transport of every intrinsic root packet. -/
theorem map_rootPowerIdeal_eq
    (E : KernelExactSquare project₀ project₁) (q : Nat) :
    Ideal.map (symmetricMap E.sourceMap) (rootPowerIdeal project₀ q) =
      rootPowerIdeal project₁ q := by
  apply le_antisymm
  · exact map_rootPowerIdeal_le project₀ project₁
      E.sourceMap E.targetMap E.commutes q
  · rw [rootPowerIdeal, Ideal.span_le]
    rintro z ⟨k₁, rfl⟩
    rcases E.kernel_surjective k₁ with ⟨k₀, hk⟩
    have hgen : (SymmetricAlgebra.ι R V₀ k₀.1) ^ q ∈
        rootPowerIdeal project₀ q :=
      rootGenerator_mem project₀ q k₀
    have hmapped := Ideal.mem_map_of_mem (symmetricMap E.sourceMap) hgen
    simpa [map_pow, symmetricMap_ι, hk] using hmapped

/-- One exact square simultaneously transports the centre and its root packet. -/
theorem map_centre_and_root_eq
    (E : KernelExactSquare project₀ project₁) (q : Nat) :
    Ideal.map (symmetricMap E.sourceMap) (kernelIdealOf project₀) =
        kernelIdealOf project₁ ∧
      Ideal.map (symmetricMap E.sourceMap) (rootPowerIdeal project₀ q) =
        rootPowerIdeal project₁ q :=
  ⟨E.map_kernelIdealOf_eq, map_rootPowerIdeal_eq E q⟩

/-- Marked permissibility is reproduced at the target because the target root
packet again lies in the same power of the transported intrinsic centre. -/
theorem target_rootPacket_permissible
    (E : KernelExactSquare project₀ project₁)
    {q : Nat} (hq : 0 < q) :
    MarkedIdeal.Permissible
      (R := SymmetricAlgebra R V₁)
      ⟨rootPowerIdeal project₁ q, q, hq⟩
      (kernelIdealOf project₁) :=
  rootPacket_permissible project₁ hq

end

end IntrinsicKernelRootPacketExactSquare
end Experimental
end PCRLean
