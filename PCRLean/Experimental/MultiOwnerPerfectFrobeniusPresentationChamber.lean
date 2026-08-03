import Mathlib
import PCRLean.Experimental.PerfectFrobeniusFinitePresentation
import PCRLean.Experimental.MultiOwnerFiniteFrobeniusPacketChamber
import PCRLean.Experimental.DualPacketBlowupChart

/-!
# Experimental multi-owner chamber from a finite pure Frobenius presentation

Over a perfect field, a finite family of pure `p^e`-forms admits a finite
covector root packet.  If the extended joint Hasse core is the ideal generated
by those pure forms and at least one form is nonzero, the recovered packet has
positive row-span rank.

The finite pure presentation is exactly the recovered packet-power ideal.
Therefore the actual affine row-span centre is nonzero, proper, finite type and
regular, permissible for every stable owner and their union, and its controlled
full root packet is terminal on every pivot chart.

This closes the perfect-field finite-pure-presentation subchamber of U5.  It
does not prove that arbitrary rank-zero Hasse cores admit such a presentation,
or treat imperfect fields, mixed higher forms or nonlinear lifting.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerPerfectFrobeniusPresentationChamber

noncomputable section

universe u v w x y

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {σ : Type w} [Fintype σ] [DecidableEq σ]
variable {κ : Type x} [Fintype κ]
variable {ω : Type y} [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))
abbrev A := MvPolynomial σ K

variable [Algebra R (A (K := K) (σ := σ))]

open PerfectFrobeniusFinitePresentation

/-- A finite pure presentation gives the finite recovered-packet realization. -/
theorem finiteRootRealization_of_purePresentation
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (coeff : κ → σ → K) (e : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        purePresentationIdeal p coeff e) :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (σ := σ))) =
      FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (rootPacket p coeff e) e :=
  hsource.trans
    (packetPowerIdeal_eq_purePresentationIdeal p coeff e).symm

/-- Complete finite-presentation escape certificate. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (coeff : κ → σ → K) (e : Nat) where
  somePureRowNonzero : ∃ i : κ,
    PerfectFrobeniusRankZeroEscape.pureFrobeniusPolynomial
      p (coeff i) e ≠ 0
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

/-- Assemble the finite-pure-presentation chamber. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (coeff : κ → σ → K) (e : Nat)
    (hnonzero : ∃ i : κ,
      PerfectFrobeniusRankZeroEscape.pureFrobeniusPolynomial
        p (coeff i) e ≠ 0)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        purePresentationIdeal p coeff e) :
    Certificate p owners coeff e := by
  let P := rootPacket p coeff e
  let OC := MultiOwnerFiniteFrobeniusPacketChamber.certificate
    p F owners hstable P e
    (finiteRootRealization_of_purePresentation
      p F owners coeff e hsource)
  have hpos := rootPacket_positive_finrank p coeff e hnonzero
  refine {
    somePureRowNonzero := hnonzero
    ownerCentre := OC
    centreNonzero := ?_
    positiveRank := hpos
    chartNonempty := ?_
    allChartTerminal := ?_
    poweredFactorization := ?_
  }
  · intro hbot
    rcases hnonzero with ⟨i, hi⟩
    have hrow := rootPacket_row_ne_zero p coeff e i hi
    have hgen : FunctionalPacketIdeal.functionalPolynomial (P i) ∈
        DualPacketAffineLinearRealization.actualIdeal P := by
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hbot] at hgen
    have hpoly : FunctionalPacketIdeal.functionalPolynomial (P i) = 0 := by
      simpa using hgen
    apply hrow
    apply FunctionalPacketIdeal.integrationMap.injective
    simpa [FunctionalPacketIdeal.integrationMap] using hpoly
  · exact DualPacketBlowupChart.nonempty_centreIndex_of_positive_finrank
      p P hpos
  · intro k
    exact DualPacketBlowupChart.transformedRootIdeal_eq_top p P k e
  · intro k i
    exact DualPacketBlowupChart.basisGenerator_pow_factorization p P k i e

end

end MultiOwnerPerfectFrobeniusPresentationChamber
end Experimental
end PCRLean
