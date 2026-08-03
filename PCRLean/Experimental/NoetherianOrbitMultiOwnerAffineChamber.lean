import Mathlib
import PCRLean.Experimental.NoetherianOrbitDualRegularCentre
import PCRLean.Experimental.MultiOwnerDualAffineFrobeniusChamber
import PCRLean.Experimental.DualPacketAffineLinearRealization

/-!
# Experimental Noetherian-orbit actual affine multi-owner chamber

A represented Noetherian operator orbit supplies a finite raw covector packet.
In a standard finite free affine chart, that packet defines an actual linear
ideal.  If the extended joint Hasse core is the actual affine `q`-root package
of the finite raw packet, the same ideal is permissible for every owner and
their finite union; it is proper and finitely generated, its quotient is
regular, and its tangent space is the persistent annihilator of the full
infinite operator orbit.

Thus all algebraic consequences after root realization are packaged in one
certificate.  The theorem does not prove universal finite-dimensional
representation, the root-realization equality, passive/boundary safety,
nonlinear chart construction, hereditary transport or globalization.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitMultiOwnerAffineChamber

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

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))
abbrev A := MvPolynomial σ K

variable [Algebra R (A (K := K) (σ := σ))]

open NoetherianOrbitDualRegularCentre
open MultiOwnerDualAffineFrobeniusChamber

/-- Combined finite-orbit and actual-affine owner certificate. -/
structure Certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    (q : Nat) (hq : 0 < q) where
  orbit : NoetherianOrbitDualRegularCentre.Certificate ops seed pair
  rootRealization :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (σ := σ))) =
      DualPacketAffineRootPackage.actualRootPowerIdeal
        (NoetherianOrbitDualRegularCentre.packetCovector pair orbit.packet) q
  ownerCentre : MultiOwnerDualAffineFrobeniusChamber.Certificate
    owners
    (NoetherianOrbitDualRegularCentre.packetCovector pair orbit.packet)
    q hq
  abstractCentre_maps_to_actualCentre :
    Ideal.map
        (DualPacketAffineLinearRealization.symToPoly
          (K := K) (σ := σ))
        orbit.centreIdeal = ownerCentre.centreIdeal
  persistentTangent_eq_actualCentreTangent :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
      ownerCentre.tangentSpace

/-- Assemble the actual affine certificate from a finite orbit certificate and
one root-realization equality. -/
noncomputable def assemble
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    {q : Nat} (hq : 0 < q)
    (hroot :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        DualPacketAffineRootPackage.actualRootPowerIdeal
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) q) :
    Certificate F owners ops seed pair q hq := by
  let OC := MultiOwnerDualAffineFrobeniusChamber.certificate
    F owners hstable
    (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet)
    hq hroot
  refine {
    orbit := C
    rootRealization := hroot
    ownerCentre := OC
    abstractCentre_maps_to_actualCentre := ?_
    persistentTangent_eq_actualCentreTangent := ?_
  }
  · rw [C.centreIdeal_eq]
    exact DualPacketAffineLinearRealization.map_centreIdeal_eq_actualIdeal
      (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet)
  · calc
      NoetherianOperatorOrbit.annihilatorVia pair
          (NoetherianOperatorOrbit.orbitModule ops seed) =
          DualPacketRegularCentre.commonTangentKernel
            (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) :=
        C.persistentTangent_eq
      _ = OC.tangentSpace := OC.tangentSpace_eq_commonKernel.symm

/-- Existence of a complete actual-affine U1--U3 certificate, conditional only
on root realization for the finite raw orbit packet. -/
theorem exists_certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Dual (K := K) (σ := σ))
    {q : Nat} (hq : 0 < q)
    (hroot : ∀ C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair,
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        DualPacketAffineRootPackage.actualRootPowerIdeal
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) q) :
    Nonempty (Certificate F owners ops seed pair q hq) := by
  rcases NoetherianOrbitDualRegularCentre.exists_certificate
    ops seed pair with ⟨C⟩
  exact ⟨assemble F owners hstable ops seed pair C hq (hroot C)⟩

end

end NoetherianOrbitMultiOwnerAffineChamber
end Experimental
end PCRLean
