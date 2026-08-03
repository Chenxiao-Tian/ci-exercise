import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.Experimental.IntrinsicKernelRootPacket
import PCRLean.Experimental.ArbitraryFiniteLinearPacketRegularCentre

/-!
# Experimental multi-owner intrinsic Frobenius chamber

Let a finite family of active owners be Hasse-stable on a realized finite
Frobenius frame.  Suppose the extension of their joint contracted core is the
intrinsic `q`-th root-power packet of a finite-dimensional linear map.  Then the
kernel ideal of that map is one actual proper finitely generated regular centre
which is permissible for every owner and for their finite union.

Unlike the coordinate chamber, no basis, coordinate support, row independence,
or split-surjection hypothesis occurs in the theorem interface.  The remaining
substantive realization hypothesis is the equality between the geometric joint
core extension and the intrinsic root-power packet.  Hereditary chart
transport, passive Tor safety, boundary transversality, and global gluing remain
separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerIntrinsicFrobeniusChamber

noncomputable section

universe u v w x y z

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {V : Type w} {W : Type x} {ω : Type y}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [FiniteDimensional K W]
variable [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

abbrev A := SymmetricAlgebra K V

variable [Algebra R (A (K := K) (V := V))]

open IntrinsicKernelIdealFunctoriality
open IntrinsicKernelRootPacket

/-- Every stable owner lies in the intrinsic root source once the joint core
extension has been identified with that source. -/
theorem owner_le_rootSource
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (V := V)) spec)
    (owners : ω → Ideal (A (K := K) (V := V)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (project : V →ₗ[K] W) (q : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (V := V))) =
        rootPowerIdeal project q)
    (i : ω) :
    owners i ≤ rootPowerIdeal project q := by
  calc
    owners i ≤
        (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (V := V))) :=
      MultiOwnerHasseCore.owner_le_jointCoreExtension
        F owners hstable i
    _ = rootPowerIdeal project q := hsource

/-- Every active owner is permissible for the same intrinsic centre. -/
theorem every_owner_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (V := V)) spec)
    (owners : ω → Ideal (A (K := K) (V := V)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (project : V →ₗ[K] W)
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (V := V))) =
        rootPowerIdeal project q)
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨owners i, q, hq⟩
      (kernelIdealOf project) := by
  exact (owner_le_rootSource F owners hstable project q hsource i).trans
    (rootPowerIdeal_le_kernelIdeal_pow project q)

/-- The finite union of all active owners is permissible for the same
intrinsic centre. -/
theorem jointOwnerIdeal_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (V := V)) spec)
    (owners : ω → Ideal (A (K := K) (V := V)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (project : V →ₗ[K] W)
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (V := V))) =
        rootPowerIdeal project q) :
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (kernelIdealOf project) := by
  have hjoint : MultiOwnerHasseCore.jointOwnerIdeal owners ≤
      rootPowerIdeal project q := by
    calc
      MultiOwnerHasseCore.jointOwnerIdeal owners ≤
          (MultiOwnerHasseCore.jointCore F owners).map
            (algebraMap R (A (K := K) (V := V))) :=
        MultiOwnerHasseCore.jointOwnerIdeal_le_jointCoreExtension
          F owners hstable
      _ = rootPowerIdeal project q := hsource
  exact hjoint.trans (rootPowerIdeal_le_kernelIdeal_pow project q)

/-- Complete algebraic certificate for the intrinsic multi-owner chamber. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (V := V)))
    (project : V →ₗ[K] W) (q : Nat) where
  everyOwnerPermissible : ∀ i : ω,
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨owners i, q, by omega⟩
      (kernelIdealOf project)
  jointOwnerPermissible :
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, by omega⟩
      (kernelIdealOf project)
  centreProper : kernelIdealOf project ≠ ⊤
  centreFiniteType : (kernelIdealOf project).FG
  centreQuotientRegular :
    IsRegularRing (A (K := K) (V := V) ⧸ kernelIdealOf project)
  quotient :
    (A (K := K) (V := V) ⧸ kernelIdealOf project) ≃+*
      SymmetricAlgebra K (LinearMap.range project)

/-- Assemble the intrinsic multi-owner regular-centre certificate. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (V := V)) spec)
    (owners : ω → Ideal (A (K := K) (V := V)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (project : V →ₗ[K] W)
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (V := V))) =
        rootPowerIdeal project q) :
    Certificate owners project q where
  everyOwnerPermissible := by
    intro i
    exact every_owner_permissible
      F owners hstable project hq hsource i
  jointOwnerPermissible :=
    jointOwnerIdeal_permissible F owners hstable project hq hsource
  centreProper :=
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_ne_top project
  centreFiniteType :=
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_fg project
  centreQuotientRegular :=
    ArbitraryFiniteLinearPacketRegularCentre.quotient_isRegularRing project
  quotient :=
    ArbitraryFiniteLinearPacketRegularCentre.quotientEquiv project

end

end MultiOwnerIntrinsicFrobeniusChamber
end Experimental
end PCRLean
