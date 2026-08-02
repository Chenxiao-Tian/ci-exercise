import Mathlib
import PCRLean.MultiOwnerSplitFrobeniusChamber
import PCRLean.MultiOwnerCoordinateFrobenius
import PCRLean.CoordinatePassiveSafety
import PCRLean.FreePassiveOwnerSafety
import PCRLean.ResidualOwnerRank
import PCRLean.Experimental.CoordinateCentreQuotient

/-!
# Experimental single-certificate closure of MLEL-002

This module collects the independently proved components of the restricted
split-coordinate Frobenius chamber into one typed certificate.  It records the
actual centre ideal, active-owner permissibility, exact coordinate quotient,
boundary-coordinate injectivity, free passive flatness, all standard chart
terminalization, overlap equality, passive-coordinate transport, and the
residual owner-support termination theorem.

The certificate remains conditional on a realized finite Frobenius frame and
an explicit coordinate-source identification.  It does not construct those
hypotheses for an arbitrary singularity and therefore is not a general
resolution theorem.
-/

namespace PCRLean
namespace Experimental
namespace MLEL002EndToEnd

noncomputable section

universe u v w x y z t

variable {R : Type u} {K : Type v}
variable [CommRing R] [CommRing K] [Nontrivial K]
variable {α : Type w} {ι : Type x} {ω : Type y} {β : Type z}
variable [DecidableEq ι]
variable [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

abbrev A := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

variable [Algebra R (A (K := K) (α := α) (ι := ι))]

/-- One semantic certificate for the complete restricted chamber. -/
structure Certificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (α := α) (ι := ι)) spec)
    (owners : ω → Ideal (A (K := K) (α := α) (ι := ι)))
    (q : Nat) (hq : 0 < q)
    (B : CoordinateBoundarySNC.Frame (β := β) (α := α))
    (Passive : Type t)
    [AddCommGroup Passive]
    [Module (A (K := K) (α := α) (ι := ι)) Passive] where
  owner_stable : ∀ i,
    DifferentialIdealSaturation.Stable F.hasseAddHom (owners i)
  source_identification :
    (MultiOwnerHasseCore.jointCore F owners).map
        (algebraMap R (A (K := K) (α := α) (ι := ι))) =
      CoordinateRootPacket.sourceIdeal
        (R := K) (α := α) (ι := ι) q
  every_owner_permissible : ∀ i : ω,
    MarkedIdeal.Permissible
      (R := A (K := K) (α := α) (ι := ι))
      ⟨owners i, q, hq⟩
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι))
  joint_owner_permissible :
    MarkedIdeal.Permissible
      (R := A (K := K) (α := α) (ι := ι))
      ⟨MultiOwnerHasseCore.jointOwnerIdeal owners, q, hq⟩
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι))
  centre_proper :
    CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι) ≠ ⊤
  centre_quotient :
    (A (K := K) (α := α) (ι := ι) ⧸
        CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ≃+*
      MvPolynomial α K
  boundary_coordinate_injective :
    Function.Injective (B.combined (ι := ι))
  passive_flat :
    Module.Flat (A (K := K) (α := α) (ι := ι)) Passive
  every_chart_terminal : ∀ k : ι,
    CoordinateRootPacket.transformedRootIdeal
      (R := K) (α := α) k q = ⊤
  every_overlap_equal : ∀ i j : ι,
    CoordinateRootPacket.transformedRootIdeal
        (R := K) (α := α) i q =
      CoordinateRootPacket.transformedRootIdeal
        (R := K) (α := α) j q
  passive_coordinate_fixed : ∀ (k : ι) (a : α),
    CoordinateBlowupChart.chartMap (R := K) (α := α) k
        (CoordinateBlowupChart.passiveVar (R := K) (ι := ι) a) =
      CoordinateBlowupChart.passiveVar (R := K) (ι := ι) a
  no_infinite_residual_owner_branch :
    ¬ ∃ f : Nat → Finset ι,
      ∀ n, ResidualOwnerRank.Step (f n) (f (n + 1))

/-- Build the complete restricted certificate from the explicit frame/source
hypotheses and a free passive module. -/
noncomputable def buildCertificate
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A (K := K) (α := α) (ι := ι)) spec)
    (owners : ω → Ideal (A (K := K) (α := α) (ι := ι)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    {q : Nat} (hq : 0 < q)
    (hsource :
      (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (α := α) (ι := ι))) =
        CoordinateRootPacket.sourceIdeal
          (R := K) (α := α) (ι := ι) q)
    (B : CoordinateBoundarySNC.Frame (β := β) (α := α))
    (Passive : Type t)
    [AddCommGroup Passive]
    [Module (A (K := K) (α := α) (ι := ι)) Passive]
    [Module.Free (A (K := K) (α := α) (ι := ι)) Passive] :
    Certificate F owners q hq B Passive := by
  obtain ⟨howners, hjoint, hproper, hcharts, hoverlaps⟩ :=
    MultiOwnerSplitFrobeniusChamber.certificate
      F owners hstable hq hsource
  exact {
    owner_stable := hstable
    source_identification := hsource
    every_owner_permissible := howners
    joint_owner_permissible := hjoint
    centre_proper := hproper
    centre_quotient :=
      CoordinateCentreQuotient.quotientEquiv
        (K := K) (α := α) (ι := ι)
    boundary_coordinate_injective :=
      MultiOwnerSplitFrobeniusChamber.boundary_coordinate_certificate
        (ι := ι) B
    passive_flat := FreePassiveOwnerSafety.flat_of_free
    every_chart_terminal := hcharts
    every_overlap_equal := hoverlaps
    passive_coordinate_fixed := fun k a =>
      CoordinatePassiveSafety.passiveVar_fixed
        (R := K) (α := α) k a
    no_infinite_residual_owner_branch :=
      ResidualOwnerRank.no_infinite_branch
  }

end

end MLEL002EndToEnd
end Experimental
end PCRLean