import Mathlib
import PCRLean.Experimental.NoetherianOrbitPacketCanonicity
import PCRLean.Experimental.NoetherianOrbitFiniteFrobeniusAffineChamber

/-!
# Experimental canonical finite Frobenius affine chamber

The finite raw packet selected by Noetherianity is noncanonical, but its actual
centre and finite Frobenius packet-power ideal are canonical.  Therefore the
strongest local U1--U3 theorem may be stated using a single canonical finite
root ideal, with no packet choice in its interface.

If the extended joint Hasse core equals that canonical ideal, Lean chooses one
finite raw orbit packet internally and produces the actual regular centre,
all-owner permissibility and the persistent tangent space.  The resulting
centre is the canonical orbit centre.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitCanonicalFrobeniusAffineChamber

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
open NoetherianOrbitFiniteFrobeniusAffineChamber

/-- Choice-free strongest local certificate. -/
structure Certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    (e : Nat) where
  local : NoetherianOrbitFiniteFrobeniusAffineChamber.Certificate
    p F owners ops seed pair e
  canonicalRootRealization :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (σ := σ))) =
      canonicalPacketPowerIdeal
        (ops := ops) (seed := seed) (pair := pair) p e
  centreIsCanonical :
    DualPacketAffineLinearRealization.actualIdeal
        (NoetherianOrbitDualRegularCentre.packetCovector pair
          local.orbit.packet) =
      canonicalActualCentre
        (ops := ops) (seed := seed) (pair := pair)

/-- Assemble the canonical certificate from one canonical finite ideal equality. -/
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
          (ops := ops) (seed := seed) (pair := pair) p e) :
    Certificate p F owners ops seed pair e := by
  let C := chosenCertificate (ops := ops) (seed := seed) (pair := pair)
  have hfinite :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        FrobeniusFiniteRootGeneration.packetPowerIdeal p
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) e :=
    hroot.trans (packetPowerIdeal_eq_canonical p C e).symm
  let L := NoetherianOrbitFiniteFrobeniusAffineChamber.assemble
    p F owners hstable ops seed pair C e hfinite
  refine {
    local := L
    canonicalRootRealization := hroot
    centreIsCanonical := ?_
  }
  exact actualCentre_eq_canonical C

/-- The canonical orbit centre is proper. -/
theorem canonicalCentre_ne_top
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
          (ops := ops) (seed := seed) (pair := pair) p e) :
    canonicalActualCentre
      (ops := ops) (seed := seed) (pair := pair) ≠ ⊤ := by
  let C := certificate p F owners hstable ops seed pair e hroot
  rw [← C.centreIsCanonical]
  exact C.local.ownerCentre.centreProper

/-- The canonical orbit centre is finitely generated. -/
theorem canonicalCentre_fg
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
          (ops := ops) (seed := seed) (pair := pair) p e) :
    (canonicalActualCentre
      (ops := ops) (seed := seed) (pair := pair)).FG := by
  let C := certificate p F owners hstable ops seed pair e hroot
  rw [← C.centreIsCanonical]
  exact C.local.ownerCentre.centreFiniteType

end

end NoetherianOrbitCanonicalFrobeniusAffineChamber
end Experimental
end PCRLean
