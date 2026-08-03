import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.Experimental.DualPacketAffineQuotient
import PCRLean.Experimental.DualPacketAffineRootPackage
import PCRLean.Experimental.DualPacketRegularCentre

/-!
# Experimental actual affine multi-owner dual Frobenius chamber

Let active owners live in a standard finite free affine chart `K[X_σ]`.  Let a
finite covector packet define its actual linear centre ideal and its actual
`q`-root package.  If the extension of the joint contracted Hasse core equals
that actual root package, then the same actual affine centre is permissible for
every owner and their finite union.  The centre is proper, finitely generated,
and has a regular quotient.

The centre tangent space is the simultaneous kernel of the packet covectors,
equivalently the annihilator of their cotangent row span.  This is a genuine
ordinary affine centre certificate, not only an associated-graded symmetric
model.  Universal root realization, nonlinear chart production, passive and
boundary safety, hereditary transform and global gluing remain explicit
frontiers.
-/

namespace PCRLean
namespace Experimental
namespace MultiOwnerDualAffineFrobeniusChamber

noncomputable section

universe u v w x y

variable {R : Type u} {K : Type v}
variable [CommRing R] [Field K]
variable {σ : Type w} [Fintype σ] [DecidableEq σ]
variable {κ : Type x} [Fintype κ]
variable {ω : Type y} [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))
abbrev A := MvPolynomial σ K

variable [Algebra R (A (K := K) (σ := σ))]

open DualPacketAffineLinearRealization
open DualPacketAffineRootPackage
open DualPacketRegularCentre

/-- Every stable owner lies in the realized actual affine root source. -/
theorem owner_le_rootSource
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Dual (K := K) (σ := σ))
    (q : Nat)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        actualRootPowerIdeal packet q)
    (i : ω) :
    owners i ≤ actualRootPowerIdeal packet q := by
  calc
    owners i ≤
        (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) :=
      MultiOwnerHasseCore.owner_le_jointCoreExtension
        F owners hstable i
    _ = actualRootPowerIdeal packet q := hsource

/-- Every active owner is permissible for the actual affine packet centre. -/
theorem every_owner_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Dual (K := K) (σ := σ))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        actualRootPowerIdeal packet q)
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A (K := K) (σ := σ))
      ⟨owners i, q, hq⟩
      (actualIdeal packet) := by
  exact (owner_le_rootSource F owners hstable packet q hsource i).trans
    (actualRootPowerIdeal_le_actualIdeal_pow packet q)

/-- The finite union of all active owners is permissible for the same actual
centre. -/
theorem jointOwnerIdeal_permissible
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Dual (K := K) (σ := σ))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        actualRootPowerIdeal packet q) :
    MarkedIdeal.Permissible
      (R := A (K := K) (σ := σ))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (actualIdeal packet) := by
  have hjoint : MultiOwnerHasseCore.jointOwnerIdeal owners ≤
      actualRootPowerIdeal packet q := by
    calc
      MultiOwnerHasseCore.jointOwnerIdeal owners ≤
          (MultiOwnerHasseCore.jointCore F owners).map
            (algebraMap R (A (K := K) (σ := σ))) :=
        MultiOwnerHasseCore.jointOwnerIdeal_le_jointCoreExtension
          F owners hstable
      _ = actualRootPowerIdeal packet q := hsource
  exact hjoint.trans (actualRootPowerIdeal_le_actualIdeal_pow packet q)

/-- Complete positive-mark actual affine centre certificate. -/
structure Certificate
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (packet : κ → Dual (K := K) (σ := σ))
    (q : Nat) (hq : 0 < q) where
  everyOwnerPermissible : ∀ i : ω,
    MarkedIdeal.Permissible
      (R := A (K := K) (σ := σ))
      ⟨owners i, q, hq⟩
      (actualIdeal packet)
  jointOwnerPermissible :
    MarkedIdeal.Permissible
      (R := A (K := K) (σ := σ))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (actualIdeal packet)
  centreProper : actualIdeal packet ≠ ⊤
  centreFiniteType : (actualIdeal packet).FG
  centreQuotientRegular :
    IsRegularRing (A (K := K) (σ := σ) ⧸ actualIdeal packet)
  quotient :
    (A (K := K) (σ := σ) ⧸ actualIdeal packet) ≃+*
      SymmetricAlgebra K
        (Dual (K := K) (σ := σ) ⧸ packetSpan packet)
  tangentSpace : Submodule K (Direction (K := K) (σ := σ))
  tangentSpace_eq_annihilator :
    tangentSpace = annihilator (packetSpan packet)
  tangentSpace_eq_commonKernel :
    tangentSpace = commonTangentKernel packet

/-- Assemble the complete actual affine multi-owner certificate. -/
noncomputable def certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (σ := σ)) spec)
    (owners : ω → Ideal (A (K := K) (σ := σ)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (packet : κ → Dual (K := K) (σ := σ))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (σ := σ))) =
        actualRootPowerIdeal packet q) :
    Certificate owners packet q hq where
  everyOwnerPermissible := by
    intro i
    exact every_owner_permissible
      F owners hstable packet hq hsource i
  jointOwnerPermissible :=
    jointOwnerIdeal_permissible F owners hstable packet hq hsource
  centreProper := DualPacketAffineQuotient.actualIdeal_ne_top packet
  centreFiniteType := DualPacketAffineQuotient.actualIdeal_fg packet
  centreQuotientRegular :=
    DualPacketAffineQuotient.quotient_isRegularRing packet
  quotient := DualPacketAffineQuotient.quotientEquiv packet
  tangentSpace := commonTangentKernel packet
  tangentSpace_eq_annihilator :=
    commonTangentKernel_eq_annihilator packet
  tangentSpace_eq_commonKernel := rfl

end

end MultiOwnerDualAffineFrobeniusChamber
end Experimental
end PCRLean
