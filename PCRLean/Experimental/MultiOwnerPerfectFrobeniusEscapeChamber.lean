import Mathlib
import PCRLean.Experimental.MultiOwnerFiniteFrobeniusPacketChamber
import PCRLean.Experimental.PerfectFrobeniusPureIdealEscape
import PCRLean.Experimental.DualPacketBlowupChart

/-!
# Experimental multi-owner perfect-field Frobenius escape chamber

Suppose a rank-zero higher diagnostic produces a nonzero pure Frobenius form

`F = ∑ i, a i * X_i^(p^e)`

over a perfect field.  Coefficientwise Frobenius inversion recovers one
nonzero covector `L` with `L^(p^e) = F`.  If the extended joint Hasse core is the
principal ideal `(F)`, then the finite-root realization hypothesis holds for
the recovered singleton packet.

Consequently the actual hyperplane centre `(L)` is nonzero, proper, finite type,
regular and permissible for every stable owner and their union.  Its row span
has positive rank, so a pivot chart exists, and the controlled full root packet
is terminal on every pivot chart.

This closes the perfect-field pure-Frobenius subchamber of U5.  It does not
prove that every rank-zero singularity yields a nonzero pure Frobenius form or
handle imperfect residue fields and mixed higher terms.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerPerfectFrobeniusEscapeChamber

noncomputable section

universe u v w y

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {σ : Type w} [Fintype σ] [DecidableEq σ]
variable {ω : Type y} [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))
abbrev A := MvPolynomial σ K

variable [Algebra R (A (K := K) (σ := σ))]

open PerfectFrobeniusRankZeroEscape
open PerfectFrobeniusPureIdealEscape

/-- Pure-root realization implies the finite singleton packet-power realization. -/
theorem finiteRootRealization_of_pure
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (coeff : σ → K) (e : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        pureFrobeniusIdeal p coeff e) :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (σ := σ))) =
      FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (rootPacket p coeff e) e :=
  hsource.trans
    (packetPowerIdeal_rootPacket_eq_pureFrobeniusIdeal p coeff e).symm

/-- Complete perfect-field pure-Frobenius escape certificate. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (coeff : σ → K) (e : Nat) where
  pureFormNonzero : pureFrobeniusPolynomial p coeff e ≠ 0
  exactRoot :
    (rootLinearPolynomial p coeff e) ^ (p ^ e) =
      pureFrobeniusPolynomial p coeff e
  ownerCentre : MultiOwnerDualAffineFrobeniusChamber.Certificate
    owners (rootPacket p coeff e) (p ^ e)
      (pow_pos (Fact.out : p.Prime).pos e)
  centreNonzero : ownerCentre.centreIdeal ≠ ⊥
  positiveRank : 0 < FiniteDimensional.finrank K
    (DualPacketRegularCentre.packetSpan (rootPacket p coeff e))
  chartNonempty : Nonempty
    (DualPacketCoordinateNormalization.CentreIndex (rootPacket p coeff e))
  allChartTerminal : ∀ k :
      DualPacketCoordinateNormalization.CentreIndex (rootPacket p coeff e),
    (DualPacketBlowupChart.rootChart (rootPacket p coeff e) k)
        .transformedRootIdeal (p ^ e) = ⊤
  poweredFactorization : ∀ k i :
      DualPacketCoordinateNormalization.CentreIndex (rootPacket p coeff e),
    DualPacketBlowupChart.chartMap (rootPacket p coeff e) k
        ((DualPacketBlowupChart.basisGenerator
          (rootPacket p coeff e) i) ^ (p ^ e)) =
      (DualPacketBlowupChart.exceptional
        (rootPacket p coeff e) k) ^ (p ^ e) *
      (DualPacketBlowupChart.controlledRoot
        (rootPacket p coeff e) k i) ^ (p ^ e)

/-- Assemble the full escape chamber from the pure principal-core equality. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (coeff : σ → K) (e : Nat)
    (hpure : pureFrobeniusPolynomial p coeff e ≠ 0)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        pureFrobeniusIdeal p coeff e) :
    Certificate p owners coeff e := by
  let P := rootPacket p coeff e
  let OC := MultiOwnerFiniteFrobeniusPacketChamber.certificate
    p F owners hstable P e
    (finiteRootRealization_of_pure p F owners coeff e hsource)
  have hpos := rootPacket_positive_finrank p coeff e hpure
  refine {
    pureFormNonzero := hpure
    exactRoot := rootLinearPolynomial_pow p coeff e
    ownerCentre := OC
    centreNonzero := ?_
    positiveRank := hpos
    chartNonempty := ?_
    allChartTerminal := ?_
    poweredFactorization := ?_
  }
  · change DualPacketAffineLinearRealization.actualIdeal P ≠ ⊥
    exact recoveredActualIdeal_ne_bot p coeff e hpure
  · exact DualPacketBlowupChart.nonempty_centreIndex_of_positive_finrank
      p P hpos
  · intro k
    exact DualPacketBlowupChart.transformedRootIdeal_eq_top p P k e
  · intro k i
    exact DualPacketBlowupChart.basisGenerator_pow_factorization p P k i e

end

end MultiOwnerPerfectFrobeniusEscapeChamber
end Experimental
end PCRLean
