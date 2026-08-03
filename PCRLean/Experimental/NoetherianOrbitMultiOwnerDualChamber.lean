import Mathlib
import PCRLean.Experimental.NoetherianOrbitDualRegularCentre
import PCRLean.Experimental.MultiOwnerDualFrobeniusChamber

/-!
# Experimental Noetherian-orbit multi-owner dual chamber

This file composes three algebraic stages:

1. a Noetherian operator orbit has a finite raw covector packet;
2. its row span defines the correctly oriented actual regular centre and its
   common tangent kernel equals the persistent infinite-orbit annihilator;
3. if the extended joint Hasse core is the packet's intrinsic `q`-root package,
   that same centre is permissible for every active owner and their union.

The only new substantive bridge exposed by the combined theorem is the root
realization equality.  The theorem remains local and linear: nonlinear lifting,
passive safety, boundary transversality, kernel-exact chart transport and global
serialization are not asserted.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitMultiOwnerDualChamber

noncomputable section

universe u v w x y z

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {D : Type w} {T : Type x} {ι : Type y} {ω : Type z}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup T] [Module K T]
variable [IsNoetherian K D]
variable [FiniteDimensional K T]
variable [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

abbrev Cotangent := Module.Dual K T
abbrev A := SymmetricAlgebra K (Cotangent (K := K) (T := T))

variable [Algebra R (A (K := K) (T := T))]

open NoetherianOrbitDualRegularCentre
open MultiOwnerDualFrobeniusChamber

/-- Combined U1--U3 algebraic certificate. -/
structure Certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Cotangent (K := K) (T := T))
    (q : Nat) (hq : 0 < q) where
  orbit : NoetherianOrbitDualRegularCentre.Certificate ops seed pair
  rootRealization :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (T := T))) =
      DualPacketRootPackage.rootPowerIdeal
        (NoetherianOrbitDualRegularCentre.packetCovector pair orbit.packet) q
  ownerCentre : MultiOwnerDualFrobeniusChamber.Certificate
    owners
    (NoetherianOrbitDualRegularCentre.packetCovector pair orbit.packet)
    q hq
  centreAgreement : orbit.centreIdeal =
    DualPacketRegularCentre.centreIdeal
      (NoetherianOrbitDualRegularCentre.packetCovector pair orbit.packet)
  persistentTangent_eq_centreTangent :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
      ownerCentre.tangentSpace

/-- Assemble a combined certificate from one finite orbit certificate and the
root realization equality for its packet. -/
noncomputable def assemble
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Cotangent (K := K) (T := T))
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    {q : Nat} (hq : 0 < q)
    (hroot :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        DualPacketRootPackage.rootPowerIdeal
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) q) :
    Certificate F owners ops seed pair q hq := by
  let OC := MultiOwnerDualFrobeniusChamber.certificate
    F owners hstable
    (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet)
    hq hroot
  refine {
    orbit := C
    rootRealization := hroot
    ownerCentre := OC
    centreAgreement := C.centreIdeal_eq
    persistentTangent_eq_centreTangent := ?_
  }
  calc
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
        DualPacketRegularCentre.commonTangentKernel
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) :=
      C.persistentTangent_eq
    _ = OC.tangentSpace := OC.tangentSpace_eq_commonKernel.symm

/-- If the root realization theorem is available for every finite raw packet
certificate, then a combined U1--U3 certificate exists. -/
theorem exists_certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Cotangent (K := K) (T := T))
    {q : Nat} (hq : 0 < q)
    (hroot : ∀ C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair,
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        DualPacketRootPackage.rootPowerIdeal
          (NoetherianOrbitDualRegularCentre.packetCovector pair C.packet) q) :
    Nonempty (Certificate F owners ops seed pair q hq) := by
  rcases NoetherianOrbitDualRegularCentre.exists_certificate
    ops seed pair with ⟨C⟩
  exact ⟨assemble F owners hstable ops seed pair C hq (hroot C)⟩

end

end NoetherianOrbitMultiOwnerDualChamber
end Experimental
end PCRLean
