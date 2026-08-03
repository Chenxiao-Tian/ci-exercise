import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PCRLean.Experimental.DualPacketAffineLinearRealization
import PCRLean.Experimental.SurjectiveFiniteDimensionalRegularCentre
import PCRLean.Experimental.FiniteDimensionalSymmetricRegularBridge

/-!
# Experimental exact affine quotient for dual-packet ideals

The actual linear packet ideal in `K[X_σ]` is the kernel of the explicit
surjection obtained by first identifying the polynomial ring with the symmetric
algebra of the cotangent space and then quotienting the cotangent space by the
packet row span.  Therefore the actual affine quotient is exactly the symmetric
algebra of the cotangent quotient and is a regular ring.

This upgrades first-order row-span data to a genuine actual affine regular
closed centre in the standard finite free chart.  The remaining nonlinear
problem is to produce and glue such coordinate charts in arbitrary prepared
regular local schemes and prove compatibility with marked transforms.
-/

namespace PCRLean
namespace Experimental
namespace DualPacketAffineQuotient

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable {κ : Type w} [Fintype κ]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))

open DualPacketAffineLinearRealization
open DualPacketRegularCentre
open SplitSurjectionSymmetricQuotient

/-- Split conormal quotient associated to the packet row span. -/
noncomputable def conormalSplit
    (packet : κ → Dual (K := K) (σ := σ)) :
    SplitSurjection
      (R := K)
      (V := Dual (K := K) (σ := σ))
      (Kmod := Dual (K := K) (σ := σ) ⧸ packetSpan packet) :=
  SurjectiveFiniteDimensionalRegularCentre.splitSurjectionOfSurjective
    (conormalQuotient packet) (conormalQuotient_surjective packet)

/-- Explicit map from the actual affine polynomial ring to the symmetric
algebra of the cotangent quotient. -/
def actualProjectAlg
    (packet : κ → Dual (K := K) (σ := σ)) :
    MvPolynomial σ K →ₐ[K]
      SymmetricAlgebra K
        (Dual (K := K) (σ := σ) ⧸ packetSpan packet) :=
  (conormalSplit packet).projectAlg.comp
    (polyToSym (K := K) (σ := σ))

/-- Evaluation of the inverse substitutions on an arbitrary symmetric
polynomial. -/
@[simp] theorem polyToSym_symToPoly
    (p : SymmetricAlgebra K (Dual (K := K) (σ := σ))) :
    polyToSym (K := K) (σ := σ)
        (symToPoly (K := K) (σ := σ) p) = p := by
  have h := congrArg
    (fun F : SymmetricAlgebra K (Dual (K := K) (σ := σ)) →ₐ[K]
        SymmetricAlgebra K (Dual (K := K) (σ := σ)) => F p)
    (polyToSym_comp_symToPoly (K := K) (σ := σ))
  simpa using h

/-- The other inverse-substitution identity on arbitrary affine polynomials. -/
@[simp] theorem symToPoly_polyToSym (p : MvPolynomial σ K) :
    symToPoly (K := K) (σ := σ)
        (polyToSym (K := K) (σ := σ) p) = p := by
  have h := congrArg
    (fun F : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => F p)
    (symToPoly_comp_polyToSym (K := K) (σ := σ))
  simpa using h

/-- The explicit affine quotient map is surjective. -/
theorem actualProjectAlg_surjective
    (packet : κ → Dual (K := K) (σ := σ)) :
    Function.Surjective (actualProjectAlg packet) := by
  intro y
  rcases (conormalSplit packet).projectAlg_surjective y with ⟨x, hx⟩
  refine ⟨symToPoly (K := K) (σ := σ) x, ?_⟩
  simpa [actualProjectAlg, hx]

/-- The kernel of the explicit affine quotient map is exactly the actual
linear packet ideal. -/
theorem ker_actualProjectAlg_eq_actualIdeal
    (packet : κ → Dual (K := K) (σ := σ)) :
    RingHom.ker (actualProjectAlg packet).toRingHom =
      actualIdeal packet := by
  apply le_antisymm
  · intro p hp
    have hzero : actualProjectAlg packet p = 0 := RingHom.mem_ker.mp hp
    have habstract :
        polyToSym (K := K) (σ := σ) p ∈
          DualPacketRegularCentre.centreIdeal packet := by
      rw [DualPacketRegularCentre.centreIdeal_eq_kernelIdeal]
      rw [← (conormalSplit packet).ker_projectAlg_eq_kernelIdeal]
      apply RingHom.mem_ker.mpr
      exact hzero
    rw [← map_centreIdeal_eq_actualIdeal]
    have hmapped := Ideal.mem_map_of_mem
      (symToPoly (K := K) (σ := σ)) habstract
    simpa using hmapped
  · rw [← map_centreIdeal_eq_actualIdeal,
      Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap]
    apply RingHom.mem_ker.mpr
    rw [DualPacketRegularCentre.centreIdeal_eq_kernelIdeal] at hp
    rw [← (conormalSplit packet).ker_projectAlg_eq_kernelIdeal] at hp
    have hzero := RingHom.mem_ker.mp hp
    simpa [actualProjectAlg] using hzero

/-- Exact first-isomorphism theorem for the actual affine packet ideal. -/
noncomputable def quotientEquiv
    (packet : κ → Dual (K := K) (σ := σ)) :
    (MvPolynomial σ K ⧸ actualIdeal packet) ≃+*
      SymmetricAlgebra K
        (Dual (K := K) (σ := σ) ⧸ packetSpan packet) :=
  (Ideal.quotEquivOfEq
      (ker_actualProjectAlg_eq_actualIdeal packet).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (actualProjectAlg packet).toRingHom)
      (actualProjectAlg_surjective packet))

/-- The actual affine packet ideal is proper. -/
theorem actualIdeal_ne_top
    (packet : κ → Dual (K := K) (σ := σ)) :
    actualIdeal packet ≠ ⊤ := by
  intro htop
  have hmem : (1 : MvPolynomial σ K) ∈ actualIdeal packet := by
    rw [htop]
    trivial
  rw [← ker_actualProjectAlg_eq_actualIdeal] at hmem
  have hzero := RingHom.mem_ker.mp hmem
  simpa using hzero

/-- The actual affine packet ideal is finitely generated. -/
theorem actualIdeal_fg
    (packet : κ → Dual (K := K) (σ := σ)) :
    (actualIdeal packet).FG :=
  IsNoetherian.noetherian _

/-- The actual affine quotient is regular. -/
theorem quotient_isRegularRing
    (packet : κ → Dual (K := K) (σ := σ)) :
    IsRegularRing (MvPolynomial σ K ⧸ actualIdeal packet) := by
  letI : IsRegularRing
      (SymmetricAlgebra K
        (Dual (K := K) (σ := σ) ⧸ packetSpan packet)) :=
    FiniteDimensionalSymmetricRegularBridge.isRegularRing
  exact IsRegularRing.of_ringEquiv (quotientEquiv packet).symm

/-- Complete actual affine regular-centre certificate. -/
structure Certificate
    (packet : κ → Dual (K := K) (σ := σ)) where
  ideal : Ideal (MvPolynomial σ K)
  ideal_eq : ideal = actualIdeal packet
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (MvPolynomial σ K ⧸ ideal) ≃+*
      SymmetricAlgebra K
        (Dual (K := K) (σ := σ) ⧸ packetSpan packet)
  quotientRegular : IsRegularRing (MvPolynomial σ K ⧸ ideal)

/-- Assemble the complete actual affine certificate. -/
noncomputable def certificate
    (packet : κ → Dual (K := K) (σ := σ)) :
    Certificate packet where
  ideal := actualIdeal packet
  ideal_eq := rfl
  proper := actualIdeal_ne_top packet
  finiteType := actualIdeal_fg packet
  quotient := quotientEquiv packet
  quotientRegular := quotient_isRegularRing packet

end

end DualPacketAffineQuotient
end Experimental
end PCRLean
