import Mathlib
import PCRLean.Experimental.FinitePacketSpanMap
import PCRLean.Experimental.NoetherianOrbitDualRegularCentre
import PCRLean.Experimental.DualPacketAffineLinearRealization
import PCRLean.Experimental.DualPacketAffineRootPackage
import PCRLean.Experimental.FrobeniusFiniteRootGeneration

/-!
# Experimental canonicity of Noetherian orbit packets

Any two finite raw packets spanning the same Noetherian operator orbit have the
same image row span under a linear covector representation.  Therefore they
define exactly the same abstract cotangent centre, actual affine centre,
persistent tangent kernel, full root package, and finite `p^e` packet-power
ideal.

This removes dependence on the noncanonical finite packet chosen by
Noetherianity.  It permits one canonical orbit centre and one canonical finite
Frobenius root ideal to be used in the subsequent geometric realization
obligation.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitPacketCanonicity

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable {D : Type v} [AddCommGroup D] [Module K D]
variable {σ : Type w} [Fintype σ] [DecidableEq σ]
variable {ι : Type x}
variable [IsNoetherian K D]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))

open NoetherianOrbitDualRegularCentre

variable {ops : ι → Module.End K D} {seed : D}
variable {pair : D →ₗ[K] Dual (K := K) (σ := σ)}

/-- The subtype enumeration of a finite packet has exactly that packet as its
range. -/
theorem range_packetSubtype
    (s : Finset D) :
    Set.range (fun d : s => (d.1 : D)) = (s : Set D) := by
  ext x
  simp

/-- Two orbit certificates have equal source packet spans. -/
theorem sourcePacketSpan_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    Submodule.span K
        (Set.range fun d : C.packet => (d.1 : D)) =
      Submodule.span K
        (Set.range fun d : E.packet => (d.1 : D)) := by
  rw [range_packetSubtype, range_packetSubtype]
  exact C.packet_spans.symm.trans E.packet_spans

/-- Two orbit certificates have exactly the same represented cotangent row
span. -/
theorem packetSpan_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    DualPacketRegularCentre.packetSpan
        (packetCovector pair C.packet) =
      DualPacketRegularCentre.packetSpan
        (packetCovector pair E.packet) := by
  exact FinitePacketSpanMap.span_image_eq_of_span_eq
    pair
    (fun d : C.packet => (d.1 : D))
    (fun d : E.packet => (d.1 : D))
    (sourcePacketSpan_eq C E)

/-- The abstract cotangent centres are packet-choice independent. -/
theorem abstractCentre_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    DualPacketRegularCentre.centreIdeal
        (packetCovector pair C.packet) =
      DualPacketRegularCentre.centreIdeal
        (packetCovector pair E.packet) :=
  DualPacketRegularCentre.centreIdeal_eq_of_span_eq
    (packetCovector pair C.packet)
    (packetCovector pair E.packet)
    (packetSpan_eq C E)

/-- The actual affine centres are packet-choice independent. -/
theorem actualCentre_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    DualPacketAffineLinearRealization.actualIdeal
        (packetCovector pair C.packet) =
      DualPacketAffineLinearRealization.actualIdeal
        (packetCovector pair E.packet) :=
  DualPacketAffineLinearRealization.actualIdeal_eq_of_span_eq
    (packetCovector pair C.packet)
    (packetCovector pair E.packet)
    (packetSpan_eq C E)

/-- The common tangent kernel is packet-choice independent. -/
theorem commonTangentKernel_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    DualPacketRegularCentre.commonTangentKernel
        (packetCovector pair C.packet) =
      DualPacketRegularCentre.commonTangentKernel
        (packetCovector pair E.packet) := by
  rw [DualPacketRegularCentre.commonTangentKernel_eq_annihilator,
    DualPacketRegularCentre.commonTangentKernel_eq_annihilator,
    packetSpan_eq C E]

/-- The full row-span root package is packet-choice independent. -/
theorem actualRootPowerIdeal_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    (q : Nat) :
    DualPacketAffineRootPackage.actualRootPowerIdeal
        (packetCovector pair C.packet) q =
      DualPacketAffineRootPackage.actualRootPowerIdeal
        (packetCovector pair E.packet) q :=
  DualPacketAffineRootPackage.actualRootPowerIdeal_eq_of_span_eq
    (packetCovector pair C.packet)
    (packetCovector pair E.packet)
    (packetSpan_eq C E) q

section Frobenius

variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- The finite named packet-power ideal is packet-choice independent. -/
theorem packetPowerIdeal_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    (e : Nat) :
    FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (packetCovector pair C.packet) e =
      FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (packetCovector pair E.packet) e := by
  rw [← FrobeniusFiniteRootGeneration.actualRootPowerIdeal_eq_packetPowerIdeal
      p (packetCovector pair C.packet) e,
    ← FrobeniusFiniteRootGeneration.actualRootPowerIdeal_eq_packetPowerIdeal
      p (packetCovector pair E.packet) e]
  exact actualRootPowerIdeal_eq C E (p ^ e)

end Frobenius

/-- A fixed noncomputable representative of the canonical finite orbit packet. -/
noncomputable def chosenCertificate :
    NoetherianOrbitDualRegularCentre.Certificate ops seed pair :=
  Classical.choice
    (NoetherianOrbitDualRegularCentre.exists_certificate ops seed pair)

/-- Canonical actual affine centre of the represented Noetherian orbit. -/
noncomputable def canonicalActualCentre : Ideal (MvPolynomial σ K) :=
  DualPacketAffineLinearRealization.actualIdeal
    (packetCovector pair (chosenCertificate (ops := ops) (seed := seed)
      (pair := pair)).packet)

/-- Every finite orbit certificate realizes the canonical actual centre. -/
theorem actualCentre_eq_canonical
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    DualPacketAffineLinearRealization.actualIdeal
        (packetCovector pair C.packet) =
      canonicalActualCentre (ops := ops) (seed := seed) (pair := pair) :=
  actualCentre_eq C
    (chosenCertificate (ops := ops) (seed := seed) (pair := pair))

/-- Canonical finite Frobenius root ideal of the represented orbit. -/
noncomputable def canonicalPacketPowerIdeal
    (p : Nat) [Fact p.Prime] [CharP K p] (e : Nat) :
    Ideal (MvPolynomial σ K) :=
  FrobeniusFiniteRootGeneration.packetPowerIdeal p
    (packetCovector pair (chosenCertificate (ops := ops) (seed := seed)
      (pair := pair)).packet) e

/-- Every finite orbit certificate realizes the canonical finite Frobenius root
ideal. -/
theorem packetPowerIdeal_eq_canonical
    (p : Nat) [Fact p.Prime] [CharP K p]
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    (e : Nat) :
    FrobeniusFiniteRootGeneration.packetPowerIdeal p
        (packetCovector pair C.packet) e =
      canonicalPacketPowerIdeal (ops := ops) (seed := seed)
        (pair := pair) p e :=
  packetPowerIdeal_eq p C
    (chosenCertificate (ops := ops) (seed := seed) (pair := pair)) e

end

end NoetherianOrbitPacketCanonicity
end Experimental
end PCRLean
