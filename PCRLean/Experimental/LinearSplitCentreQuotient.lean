import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PCRLean.LinearCoordinateChange
import PCRLean.CoordinateBlowupChart
import PCRLean.CoordinateCentreProper
import PCRLean.Experimental.CoordinateCentreQuotient

/-!
# Experimental linear split-centre quotient

A full linear frame gives an actual polynomial automorphism.  Transporting the
coordinate-centre ideal through that automorphism produces an actual linear
centre.  The quotient by the transported centre is ring-equivalent to the
coordinate quotient and hence to the passive polynomial ring.

This removes literal coordinate-generator dependence inside the split linear
chamber.  It does not prove that an arbitrary Frobenius/Fitting core admits a
full linear frame or that such frames glue over arbitrary overlaps.
-/

namespace PCRLean
namespace Experimental
namespace LinearSplitCentreQuotient

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]

abbrev P := MvPolynomial (α ⊕ ι) K

/-- The standard coordinate-centre ideal. -/
def coordinateCentreIdeal : Ideal (P (K := K) (α := α) (ι := ι)) :=
  CoordinateBlowupChart.centreIdeal
    (R := K) (α := α) (ι := ι)

/-- Transport the actual coordinate centre through a full linear polynomial
automorphism. -/
def linearCentreIdeal
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι)) :
    Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.map F.forward
    (coordinateCentreIdeal (K := K) (α := α) (ι := ι))

/-- The polynomial automorphism induces an equivalence between the coordinate
quotient and the transported linear-centre quotient. -/
noncomputable def coordinateQuotientEquivLinear
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι)) :
    (P (K := K) (α := α) (ι := ι) ⧸
        coordinateCentreIdeal (K := K) (α := α) (ι := ι)) ≃+*
      (P (K := K) (α := α) (ι := ι) ⧸
        linearCentreIdeal (K := K) (α := α) (ι := ι) F) :=
  Ideal.quotientEquiv
    (coordinateCentreIdeal (K := K) (α := α) (ι := ι))
    (linearCentreIdeal (K := K) (α := α) (ι := ι) F)
    F.polynomialEquiv.toRingEquiv
    (by rfl)

/-- Exact quotient theorem for every centre obtained from a full linear split
frame. -/
noncomputable def linearCentreQuotientEquiv
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι)) :
    (P (K := K) (α := α) (ι := ι) ⧸
        linearCentreIdeal (K := K) (α := α) (ι := ι) F) ≃+*
      MvPolynomial α K :=
  (coordinateQuotientEquivLinear
      (K := K) (α := α) (ι := ι) F).symm.trans
    (CoordinateCentreQuotient.quotientEquiv
      (K := K) (α := α) (ι := ι))

/-- The transported linear centre remains proper. -/
theorem linearCentreIdeal_ne_top
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι)) :
    linearCentreIdeal (K := K) (α := α) (ι := ι) F ≠ ⊤ := by
  intro htop
  have hmap := congrArg
    (fun J : Ideal (P (K := K) (α := α) (ι := ι)) =>
      Ideal.map F.polynomialEquiv.symm.toRingEquiv J) htop
  have hcoord :
      coordinateCentreIdeal (K := K) (α := α) (ι := ι) = ⊤ := by
    simpa [linearCentreIdeal, coordinateCentreIdeal] using hmap
  exact CoordinateCentreProper.centreIdeal_ne_top
    (K := K) (α := α) (ι := ι) hcoord

end

end LinearSplitCentreQuotient
end Experimental
end PCRLean