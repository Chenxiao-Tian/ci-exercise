import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.FrobeniusNormalLocalCoordinateModel
import PCRLean.Experimental.ReducedCoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity

/-!
# Faithfully flat reduced local models

The previous files identify reducedness of the coefficient ring as the exact
obstruction to Frobenius heredity for coordinate and polynomial graph centres.
This file combines that local theorem with faithfully flat ideal descent.

Consequently, an arbitrary centre ideal is Frobenius-normal as soon as it has a
faithfully flat local model in which its pullback is a coordinate or graph
centre over a reduced characteristic-`p` ring.

This is the precise algebraic interface expected from geometry.  The remaining
scheme-level theorem is an existence theorem for such a finite étale/fpqc graph
atlas around every regular centre, together with compatibility with owners,
boundaries and controlled transforms.
-/

namespace PCRLean
namespace Experimental
namespace ReducedFrobeniusNormalLocalModel

noncomputable section

universe u v w x y

variable {A : Type u} [CommRing A]

section Coordinate

variable {R : Type v} [CommRing R] [IsReduced R]
variable {α : Type w} {ι : Type x}
variable [DecidableEq α] [DecidableEq ι]
variable (p : Nat) [Fact p.Prime] [CharP R p]

abbrev CoordinateRing :=
  CoordinateBlowupChart.P (R := R) (α := α) (ι := ι)

variable [Algebra A (CoordinateRing (R := R) (α := α) (ι := ι))]
variable [Module.FaithfullyFlat A
  (CoordinateRing (R := R) (α := α) (ι := ι))]

/-- A faithfully flat reduced coordinate model makes the original ideal
Frobenius-normal. -/
theorem reflects_of_reducedCoordinateModel
    (I : Ideal A)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := CoordinateRing (R := R) (α := α) (ι := ι)) I =
      CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι)) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact FrobeniusNormalLocalCoordinateModel.reflects_of_model
    (B := CoordinateRing (R := R) (α := α) (ι := ι))
    p I
    (CoordinateBlowupChart.centreIdeal
      (R := R) (α := α) (ι := ι))
    hmodel
    (ReducedCoordinateCentreExactFrobeniusHeredity.coordinateCentre_reflects
      (R := R) (α := α) (ι := ι) p)

/-- Exact marked heredity in the base ring from a reduced coordinate model. -/
theorem power_mem_scaled_iff_of_reducedCoordinateModel
    (I : Ideal A)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := CoordinateRing (R := R) (α := α) (ι := ι)) I =
      CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι))
    (e mark : Nat) (a : A) :
    a ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ a ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflects_of_reducedCoordinateModel
      (R := R) (α := α) (ι := ι) p I hmodel)
    e mark a

end Coordinate

section Graph

variable {R : Type v} [CommRing R] [IsReduced R]
variable {ι : Type y} [DecidableEq ι]
variable (p : Nat) [Fact p.Prime] [CharP R p]

abbrev GraphRing := MvPolynomial ι R

variable [Algebra A (GraphRing (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (GraphRing (R := R) (ι := ι))]

/-- A faithfully flat reduced graph model makes the original ideal
Frobenius-normal. -/
theorem reflects_of_reducedGraphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := GraphRing (R := R) (ι := ι)) I =
      ReducedPolynomialGraphCentreHeredity.graphIdeal h) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact FrobeniusNormalLocalCoordinateModel.reflects_of_model
    (B := GraphRing (R := R) (ι := ι))
    p I
    (ReducedPolynomialGraphCentreHeredity.graphIdeal h)
    hmodel
    (ReducedPolynomialGraphCentreHeredity
      .graphIdeal_reflectsFrobeniusPowers p h)

/-- Exact marked heredity in the base ring from a reduced graph model. -/
theorem power_mem_scaled_iff_of_reducedGraphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := GraphRing (R := R) (ι := ι)) I =
      ReducedPolynomialGraphCentreHeredity.graphIdeal h)
    (e mark : Nat) (a : A) :
    a ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ a ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflects_of_reducedGraphModel
      (R := R) (ι := ι) p I h hmodel)
    e mark a

end Graph

end

end ReducedFrobeniusNormalLocalModel
end Experimental
end PCRLean
