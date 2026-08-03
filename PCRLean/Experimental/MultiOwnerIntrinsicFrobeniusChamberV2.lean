import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.Experimental.IntrinsicKernelRootPacket
import PCRLean.Experimental.ArbitraryFiniteLinearPacketRegularCentre

/-!
# Experimental positive-mark intrinsic multi-owner Frobenius chamber

This is the positive-mark typed form of the intrinsic multi-owner chamber.  A
finite Hasse-stable owner family is controlled by one finite-dimensional linear
packet whenever the extended joint contracted core equals the intrinsic
`q`-root packet of that map.  The positive mark is an explicit parameter of the
certificate and is never inferred or hidden.

The resulting kernel ideal is actual, proper and finitely generated; its
quotient is regular; and it is permissible for every owner and their finite
union.  The root-realization equality, passive safety, boundary compatibility,
hereditary exact squares, and globalization remain explicit hypotheses or
later obligations.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerIntrinsicFrobeniusChamberV2

noncomputable section

universe u v w x y

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

/-- Every stable owner lies in the realized intrinsic root source. -/
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

/-- Every active owner is permissible for the intrinsic kernel centre. -/
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

/-- The finite union of all active owners is permissible for the same centre. -/
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

/-- Complete positive-mark algebraic certificate. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (V := V)))
    (project : V →ₗ[K] W) (q : Nat) (hq : 0 < q) where
  everyOwnerPermissible : ∀ i : ω,
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨owners i, q, hq⟩
      (kernelIdealOf project)
  jointOwnerPermissible :
    MarkedIdeal.Permissible
      (R := A (K := K) (V := V))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (kernelIdealOf project)
  centreProper : kernelIdealOf project ≠ ⊤
  centreFiniteType : (kernelIdealOf project).FG
  centreQuotientRegular :
    IsRegularRing (A (K := K) (V := V) ⧸ kernelIdealOf project)
  quotient :
    (A (K := K) (V := V) ⧸ kernelIdealOf project) ≃+*
      SymmetricAlgebra K (LinearMap.range project)

/-- Assemble the positive-mark intrinsic multi-owner certificate. -/
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
    Certificate owners project q hq where
  everyOwnerPermissible := by
    intro i
    exact every_owner_permissible
      F owners hstable project hq hsource i
  jointOwnerPermissible :=
    jointOwnerIdeal_permissible F owners hstable project hq hsource
  centreProper := by
    change ArbitraryFiniteLinearPacketRegularCentre.centreIdeal project ≠ ⊤
    exact ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_ne_top project
  centreFiniteType := by
    change (ArbitraryFiniteLinearPacketRegularCentre.centreIdeal project).FG
    exact ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_fg project
  centreQuotientRegular := by
    change IsRegularRing
      (A (K := K) (V := V) ⧸
        ArbitraryFiniteLinearPacketRegularCentre.centreIdeal project)
    exact ArbitraryFiniteLinearPacketRegularCentre.quotient_isRegularRing project
  quotient := by
    change
      (A (K := K) (V := V) ⧸
        ArbitraryFiniteLinearPacketRegularCentre.centreIdeal project) ≃+*
        SymmetricAlgebra K (LinearMap.range project)
    exact ArbitraryFiniteLinearPacketRegularCentre.quotientEquiv project

end

end MultiOwnerIntrinsicFrobeniusChamberV2
end Experimental
end PCRLean
