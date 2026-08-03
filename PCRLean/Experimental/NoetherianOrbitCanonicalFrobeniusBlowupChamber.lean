import Mathlib
import PCRLean.Experimental.NoetherianOrbitCanonicalFrobeniusAffineChamber
import PCRLean.Experimental.DualPacketBlowupChart

/-!
# Experimental canonical Frobenius chamber with actual blowup charts

Starting from the canonical finite Frobenius root-realization equality, the
canonical orbit centre is an actual affine regular permissible centre.  If its
cotangent row span has positive rank, choose a basis of that span and conjugate
standard coordinate blowup charts back to the original affine ring.

Every basis root has exact exceptional factorization and the controlled full
`p^e`-root packet is terminal on every pivot chart.  Thus the represented
positive-rank linear chamber closes U1--U4 locally.  Rank zero, passive/boundary
heredity beyond the linear chart, nonlinear lifting and globalization remain
separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitCanonicalFrobeniusBlowupChamber

noncomputable section

universe u v w x y z

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {D : Type w} [AddCommGroup D] [Module K D]
variable {σ : Type x} [Fintype σ] [DecidableEq σ]
variable {ι : Type y}
variable {ω : Type z} [Fintype ω] [DecidableEq ω]
variable [IsNoetherian K D]
variable {spec : List (Nat × R)}
variable (p : Nat) [Fact p.Prime] [CharP K p]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))
abbrev A := MvPolynomial σ K

variable [Algebra R (A (K := K) (σ := σ))]

open NoetherianOrbitPacketCanonicity
open NoetherianOrbitCanonicalFrobeniusAffineChamber
open NoetherianOrbitDualRegularCentre

/-- The chosen finite raw orbit packet used internally by the canonical
construction. -/
noncomputable def canonicalPacket
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ)) :
    Finset D :=
  (chosenCertificate (ops := ops) (seed := seed) (pair := pair)).packet

/-- Its represented covector packet. -/
def canonicalCovectorPacket
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ)) :
    canonicalPacket ops seed pair → Dual (K := K) (σ := σ) :=
  packetCovector pair (canonicalPacket ops seed pair)

/-- Canonical cotangent row-span rank of the represented orbit. -/
def canonicalCentreRank
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ)) : Nat :=
  FiniteDimensional.finrank K
    (DualPacketRegularCentre.packetSpan
      (canonicalCovectorPacket ops seed pair))

/-- Complete local positive-rank U1--U4 certificate. -/
structure Certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    (e : Nat) where
  local : NoetherianOrbitCanonicalFrobeniusAffineChamber.Certificate
    p F owners ops seed pair e
  positiveRank : 0 < canonicalCentreRank ops seed pair
  chartNonempty : Nonempty
    (DualPacketCoordinateNormalization.CentreIndex
      (canonicalCovectorPacket ops seed pair))
  canonicalRoot_eq_basisPowerIdeal :
    canonicalPacketPowerIdeal
        (ops := ops) (seed := seed) (pair := pair) p e =
      FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (DualPacketCoordinateNormalization.centreCovector
          (canonicalCovectorPacket ops seed pair)) e
  allChartTerminal : ∀ k :
      DualPacketCoordinateNormalization.CentreIndex
        (canonicalCovectorPacket ops seed pair),
    (DualPacketBlowupChart.rootChart
      (canonicalCovectorPacket ops seed pair) k).transformedRootIdeal
        (p ^ e) = ⊤
  poweredFactorization : ∀ k i :
      DualPacketCoordinateNormalization.CentreIndex
        (canonicalCovectorPacket ops seed pair),
    DualPacketBlowupChart.chartMap
        (canonicalCovectorPacket ops seed pair) k
        ((DualPacketBlowupChart.basisGenerator
          (canonicalCovectorPacket ops seed pair) i) ^ (p ^ e)) =
      (DualPacketBlowupChart.exceptional
        (canonicalCovectorPacket ops seed pair) k) ^ (p ^ e) *
      (DualPacketBlowupChart.controlledRoot
        (canonicalCovectorPacket ops seed pair) k i) ^ (p ^ e)

/-- Assemble the canonical local U1--U4 blowup certificate. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    (e : Nat)
    (hroot :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        canonicalPacketPowerIdeal
          (ops := ops) (seed := seed) (pair := pair) p e)
    (hpos : 0 < canonicalCentreRank ops seed pair) :
    Certificate p F owners ops seed pair e := by
  let P := canonicalCovectorPacket ops seed pair
  let L := NoetherianOrbitCanonicalFrobeniusAffineChamber.certificate
    p F owners hstable ops seed pair e hroot
  have hrootBasis :
      canonicalPacketPowerIdeal
          (ops := ops) (seed := seed) (pair := pair) p e =
        FrobeniusFiniteRootGeneration.packetPowerIdeal p
          (DualPacketCoordinateNormalization.centreCovector P) e := by
    change FrobeniusFiniteRootGeneration.packetPowerIdeal p P e = _
    rw [← FrobeniusFiniteRootGeneration.actualRootPowerIdeal_eq_packetPowerIdeal
      p P e]
    exact DualPacketBlowupChart.actualRootPowerIdeal_eq_basisPowerIdeal p P e
  refine {
    local := L
    positiveRank := hpos
    chartNonempty := ?_
    canonicalRoot_eq_basisPowerIdeal := hrootBasis
    allChartTerminal := ?_
    poweredFactorization := ?_
  }
  · exact DualPacketBlowupChart.nonempty_centreIndex_of_positive_finrank
      p P hpos
  · intro k
    exact DualPacketBlowupChart.transformedRootIdeal_eq_top p P k e
  · intro k i
    exact DualPacketBlowupChart.basisGenerator_pow_factorization p P k i e

end

end NoetherianOrbitCanonicalFrobeniusBlowupChamber
end Experimental
end PCRLean
