import Mathlib
import PCRLean.MarkedIdeal
import PCRLean.Experimental.DualPacketAffineLinearRealization
import PCRLean.Experimental.DualPacketRootPackage

/-!
# Experimental affine realization of dual-packet root packages

The correctly oriented cotangent row-span root package has an actual affine
realization: integrate every row-span covector to its linear polynomial and
take its `q`-th power.  This actual root ideal lies in the `q`-th power of the
actual affine centre ideal and is therefore marked permissible.

The affine root package is exactly the image of the abstract cotangent root
package under the explicit symmetric-algebra/polynomial-ring equivalence.  It
depends only on the packet row span.
-/

namespace PCRLean
namespace Experimental
namespace DualPacketAffineRootPackage

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable {κ : Type w} [Fintype κ]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))

open DualPacketAffineLinearRealization
open DualPacketRegularCentre

/-- Actual affine `q`-root package of the packet row span. -/
def actualRootPowerIdeal
    (packet : κ → Dual (K := K) (σ := σ)) (q : Nat) :
    Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun f : packetSpan packet =>
    (FunctionalPacketIdeal.functionalPolynomial f.1) ^ q)

/-- Every row-span root power belongs to the actual root package. -/
theorem rootGenerator_mem
    (packet : κ → Dual (K := K) (σ := σ))
    (q : Nat) (f : packetSpan packet) :
    (FunctionalPacketIdeal.functionalPolynomial f.1) ^ q ∈
      actualRootPowerIdeal packet q := by
  apply Ideal.subset_span
  exact ⟨f, rfl⟩

/-- The actual root package lies in the matching power of the actual affine
centre ideal. -/
theorem actualRootPowerIdeal_le_actualIdeal_pow
    (packet : κ → Dual (K := K) (σ := σ)) (q : Nat) :
    actualRootPowerIdeal packet q ≤ (actualIdeal packet) ^ q := by
  rw [actualRootPowerIdeal, Ideal.span_le]
  rintro z ⟨f, rfl⟩
  exact Ideal.pow_mem_pow
    (functionalPolynomial_mem_actualIdeal_of_mem_span packet f.2) q

/-- Marked permissibility in the actual affine coordinate ring. -/
theorem actualRootPacket_permissible
    (packet : κ → Dual (K := K) (σ := σ))
    {q : Nat} (hq : 0 < q) :
    MarkedIdeal.Permissible
      (R := MvPolynomial σ K)
      ⟨actualRootPowerIdeal packet q, q, hq⟩
      (actualIdeal packet) :=
  actualRootPowerIdeal_le_actualIdeal_pow packet q

/-- The abstract cotangent root package maps exactly to the actual affine root
package. -/
theorem map_rootPowerIdeal_eq_actualRootPowerIdeal
    (packet : κ → Dual (K := K) (σ := σ)) (q : Nat) :
    Ideal.map (symToPoly (K := K) (σ := σ))
        (DualPacketRootPackage.rootPowerIdeal packet q) =
      actualRootPowerIdeal packet q := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap,
      DualPacketRootPackage.rootPowerIdeal, Ideal.span_le]
    rintro z ⟨f, rfl⟩
    rw [Ideal.mem_comap]
    change symToPoly (K := K) (σ := σ)
        ((SymmetricAlgebra.ι K (Dual (K := K) (σ := σ)) f.1) ^ q) ∈
      actualRootPowerIdeal packet q
    rw [map_pow, symToPoly_ι]
    exact rootGenerator_mem packet q f
  · rw [actualRootPowerIdeal, Ideal.span_le]
    rintro z ⟨f, rfl⟩
    rw [← map_pow, ← symToPoly_ι]
    apply Ideal.mem_map_of_mem
    exact DualPacketRootPackage.rootGenerator_mem packet q f

/-- Equal row spans define equal actual affine root packages, even for packets
with different finite index types. -/
theorem actualRootPowerIdeal_eq_of_span_eq
    {λ : Type*} [Fintype λ]
    (p : κ → Dual (K := K) (σ := σ))
    (r : λ → Dual (K := K) (σ := σ))
    (hspan : packetSpan p = packetSpan r)
    (q : Nat) :
    actualRootPowerIdeal p q = actualRootPowerIdeal r q := by
  unfold actualRootPowerIdeal
  rw [hspan]

end

end DualPacketAffineRootPackage
end Experimental
end PCRLean
