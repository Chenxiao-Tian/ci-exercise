import Mathlib
import PCRLean.MultiOwnerHasseCore
import PCRLean.FrobeniusPowerIdeal
import PCRLean.SplitFrobeniusChamber
import PCRLean.CoordinateCentreKernelBridge
import PCRLean.CoordinateBoundarySNC
import PCRLean.CoordinateTerminalOverlap

/-!
# Multi-owner split Frobenius chamber

This file combines exact joint Hasse descent with a coordinate realization of
the joint root core. The aggregate active owner ideal becomes the coordinate
Frobenius-power packet, so blowing up the full coordinate root centre makes the
joint controlled packet terminal on every standard chart in one step.
-/

namespace PCRLean
namespace MultiOwnerSplitFrobeniusChamber

noncomputable section

universe u v w x y

variable {R : Type u} {K : Type v}
variable [CommRing R] [CommRing K] [Nontrivial K]
variable (p e : Nat) [ExpChar K p]
variable {α : Type w} {ι : Type x} {ω : Type y}
variable [DecidableEq ι]
variable {spec : List (Nat × R)}

abbrev A := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

variable [Algebra R (A (K := K) (α := α) (ι := ι))]

abbrev Frame := MultiHasseOnlyDescent.RealizedFrame

/-- Exact identification of the joint active ideal with the coordinate
`p^e`-power source packet. -/
theorem jointOwnerIdeal_eq_coordinateSource
    (F : Frame
      (R := R) (A := A (K := K) (α := α) (ι := ι)) spec)
    (S : FrobeniusPowerIdeal.RootEquiv
      (A := A (K := K) (α := α) (ι := ι)) p e (R := R))
    (owners : ω → Ideal (A (K := K) (α := α) (ι := ι)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (hcoord : S.rootIdeal (MultiOwnerHasseCore.jointCore F owners) =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) :
    MultiOwnerHasseCore.jointOwnerIdeal owners =
      CoordinateCentrePrincipalization.sourceIdeal
        (R := K) (α := α) (ι := ι) (p ^ e) := by
  calc
    MultiOwnerHasseCore.jointOwnerIdeal owners =
        (MultiOwnerHasseCore.jointCore F owners).map
          (algebraMap R (A (K := K) (α := α) (ι := ι))) :=
      MultiOwnerHasseCore.jointOwnerIdeal_eq_map_jointCore
        F owners hstable
    _ = CoordinateCentrePrincipalization.sourceIdeal
          (R := K) (α := α) (ι := ι) (p ^ e) :=
      SplitFrobeniusChamber.baseExtension_eq_coordinateSource
        (K := K) (α := α) (ι := ι) p e S
        (MultiOwnerHasseCore.jointCore F owners) hcoord

/-- Every individual owner is permissible for the same coordinate centre. -/
theorem every_owner_permissible
    (hp : 0 < p)
    (F : Frame
      (R := R) (A := A (K := K) (α := α) (ι := ι)) spec)
    (S : FrobeniusPowerIdeal.RootEquiv
      (A := A (K := K) (α := α) (ι := ι)) p e (R := R))
    (owners : ω → Ideal (A (K := K) (α := α) (ι := ι)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (hcoord : S.rootIdeal (MultiOwnerHasseCore.jointCore F owners) =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι))
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A (K := K) (α := α) (ι := ι))
      ⟨owners i, p ^ e, pow_pos hp e⟩
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) := by
  have howner : owners i ≤
      MultiOwnerHasseCore.jointOwnerIdeal owners :=
    le_iSup (fun j => owners j) i
  have hjoint : MultiOwnerHasseCore.jointOwnerIdeal owners ≤
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) ^ (p ^ e) := by
    rw [jointOwnerIdeal_eq_coordinateSource
      (K := K) (α := α) (ι := ι) p e F S owners hstable hcoord]
    exact CoordinateCentrePrincipalization.sourceIdeal_le_centre_pow
      (R := K) (α := α) (ι := ι) (p ^ e)
  exact howner.trans hjoint

/-- Complete restricted certificate: exact joint source, simultaneous active
permissibility, proper actual centre, explicit quotient, all-chart terminality,
and terminal overlap equality. -/
theorem certificate
    (hp : 0 < p)
    (F : Frame
      (R := R) (A := A (K := K) (α := α) (ι := ι)) spec)
    (S : FrobeniusPowerIdeal.RootEquiv
      (A := A (K := K) (α := α) (ι := ι)) p e (R := R))
    (owners : ω → Ideal (A (K := K) (α := α) (ι := ι)))
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (hcoord : S.rootIdeal (MultiOwnerHasseCore.jointCore F owners) =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) :
    MultiOwnerHasseCore.jointOwnerIdeal owners =
        CoordinateCentrePrincipalization.sourceIdeal
          (R := K) (α := α) (ι := ι) (p ^ e) ∧
      (∀ i : ω,
        MarkedIdeal.Permissible
          (R := A (K := K) (α := α) (ι := ι))
          ⟨owners i, p ^ e, pow_pos hp e⟩
          (CoordinateBlowupChart.centreIdeal
            (R := K) (α := α) (ι := ι))) ∧
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) ≠ ⊤ ∧
      Nonempty
        ((A (K := K) (α := α) (ι := ι) ⧸
            CoordinateBlowupChart.centreIdeal
              (R := K) (α := α) (ι := ι)) ≃+*
          MvPolynomial α K) ∧
      (∀ k : ι,
        CoordinateCentrePrincipalization.transformedRootIdeal
          (R := K) (α := α) k (p ^ e) = ⊤) ∧
      (∀ i j : ι,
        CoordinateCentrePrincipalization.transformedRootIdeal
            (R := K) (α := α) i (p ^ e) =
          CoordinateCentrePrincipalization.transformedRootIdeal
            (R := K) (α := α) j (p ^ e)) := by
  refine ⟨jointOwnerIdeal_eq_coordinateSource
      (K := K) (α := α) (ι := ι) p e F S owners hstable hcoord,
    ?_,
    CoordinateCentreKernelBridge.centreIdeal_ne_top
      (K := K) (α := α) (ι := ι),
    ⟨CoordinateCentreKernelBridge.quotientEquiv
      (K := K) (α := α) (ι := ι)⟩,
    ?_, ?_⟩
  · intro i
    exact every_owner_permissible
      (K := K) (α := α) (ι := ι) p e hp F S owners hstable hcoord i
  · intro k
    exact CoordinateCentrePrincipalization.transformedRootIdeal_eq_top
      (R := K) (α := α) k (p ^ e)
  · intro i j
    exact CoordinateTerminalOverlap.transformedRootIdeal_eq
      (R := K) (α := α) i j (p ^ e)

end

end MultiOwnerSplitFrobeniusChamber
end PCRLean
