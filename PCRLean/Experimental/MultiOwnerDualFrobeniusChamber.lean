import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.Experimental.DualPacketRegularCentre
import PCRLean.Experimental.DualPacketRootPackage

/-!
# Experimental correctly oriented multi-owner dual Frobenius chamber

Let a finite family of active owners be Hasse-stable on a realized finite
Frobenius frame in the cotangent symmetric algebra.  Suppose the extension of
their joint contracted core equals the correctly oriented `q`-root package of
a finite covector packet.  Then the row-span ideal of that packet is one actual
proper finitely generated regular centre, permissible for every owner and for
their finite union.

The centre tangent space is the annihilator of the packet row span, equivalently
the simultaneous kernel of the packet covectors.  This statement keeps tangent
and cotangent roles separate.  Root realization, nonlinear lifting, passive
Tor safety, boundary transversality, hereditary chart transport and global
gluing remain later obligations.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerDualFrobeniusChamber

noncomputable section

universe u v w x y

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {T : Type w} [AddCommGroup T] [Module K T]
variable [FiniteDimensional K T]
variable {κ : Type x} [Fintype κ]
variable {ω : Type y} [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

abbrev Cotangent := Module.Dual K T
abbrev A := SymmetricAlgebra K (Cotangent (K := K) (T := T))

variable [Algebra R (A (K := K) (T := T))]

open DualPacketRegularCentre
open DualPacketRootPackage

/-- Every stable owner lies in the realized dual root source. -/
theorem owner_le_rootSource
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Cotangent (K := K) (T := T)) (q : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        rootPowerIdeal packet q)
    (i : ω) :
    owners i ≤ rootPowerIdeal packet q := by
  calc
    owners i ≤
        (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) :=
      MultiOwnerHasseCore.owner_le_jointCoreExtension
        F owners hstable i
    _ = rootPowerIdeal packet q := hsource

/-- Every active owner is permissible for the row-span centre. -/
theorem every_owner_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Cotangent (K := K) (T := T))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        rootPowerIdeal packet q)
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A (K := K) (T := T))
      ⟨owners i, q, hq⟩
      (centreIdeal packet) := by
  exact (owner_le_rootSource F owners hstable packet q hsource i).trans
    (rootPowerIdeal_le_centreIdeal_pow packet q)

/-- The finite union of all active owners is permissible for the same centre. -/
theorem jointOwnerIdeal_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Cotangent (K := K) (T := T))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        rootPowerIdeal packet q) :
    MarkedIdeal.Permissible
      (R := A (K := K) (T := T))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (centreIdeal packet) := by
  have hjoint : MultiOwnerHasseCore.jointOwnerIdeal owners ≤
      rootPowerIdeal packet q := by
    calc
      MultiOwnerHasseCore.jointOwnerIdeal owners ≤
          (MultiOwnerHasseCore.jointCore F owners).map
            (algebraMap R (A (K := K) (T := T))) :=
        MultiOwnerHasseCore.jointOwnerIdeal_le_jointCoreExtension
          F owners hstable
      _ = rootPowerIdeal packet q := hsource
  exact hjoint.trans (rootPowerIdeal_le_centreIdeal_pow packet q)

/-- Complete correctly oriented positive-mark certificate. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (T := T)))
    (packet : κ → Cotangent (K := K) (T := T))
    (q : Nat) (hq : 0 < q) where
  everyOwnerPermissible : ∀ i : ω,
    MarkedIdeal.Permissible
      (R := A (K := K) (T := T))
      ⟨owners i, q, hq⟩
      (centreIdeal packet)
  jointOwnerPermissible :
    MarkedIdeal.Permissible
      (R := A (K := K) (T := T))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (centreIdeal packet)
  centreProper : centreIdeal packet ≠ ⊤
  centreFiniteType : (centreIdeal packet).FG
  centreQuotientRegular :
    IsRegularRing (A (K := K) (T := T) ⧸ centreIdeal packet)
  quotient :
    (A (K := K) (T := T) ⧸ centreIdeal packet) ≃+*
      SymmetricAlgebra K
        (Cotangent (K := K) (T := T) ⧸ packetSpan packet)
  tangentSpace : Submodule K T
  tangentSpace_eq : tangentSpace = annihilator (packetSpan packet)
  tangentSpace_eq_commonKernel :
    tangentSpace = commonTangentKernel packet

/-- Assemble the correctly oriented multi-owner regular-centre certificate. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (T := T)) spec)
    (owners : ω → Ideal (A (K := K) (T := T)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Cotangent (K := K) (T := T))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (T := T))) =
        rootPowerIdeal packet q) :
    Certificate owners packet q hq where
  everyOwnerPermissible := by
    intro i
    exact every_owner_permissible
      F owners hstable packet hq hsource i
  jointOwnerPermissible :=
    jointOwnerIdeal_permissible F owners hstable packet hq hsource
  centreProper := DualPacketRegularCentre.centreIdeal_ne_top packet
  centreFiniteType := DualPacketRegularCentre.centreIdeal_fg packet
  centreQuotientRegular :=
    DualPacketRegularCentre.quotient_isRegularRing packet
  quotient := DualPacketRegularCentre.quotientEquiv packet
  tangentSpace := commonTangentKernel packet
  tangentSpace_eq := commonTangentKernel_eq_annihilator packet
  tangentSpace_eq_commonKernel := rfl

end

end MultiOwnerDualFrobeniusChamber
end Experimental
end PCRLean
