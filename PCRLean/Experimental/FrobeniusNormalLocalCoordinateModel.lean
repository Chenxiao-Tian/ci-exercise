import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.FrobeniusNormalCentre
import PCRLean.Experimental.FrobeniusNormalFaithfullyFlatDescent
import PCRLean.Experimental.AffineLinearFrameExactFrobeniusHeredity
import PCRLean.Experimental.PolynomialGraphCentreHeredity

/-!
# Faithfully flat coordinate and graph models for Frobenius-normal centres

Suppose a centre ideal `I ⊂ A` becomes, after a faithfully flat extension
`A → B`, an ideal `J ⊂ B` whose power filtration reflects prime-power roots.
Then `I` reflects them as well.

Concrete specializations are recorded for:

* a standard positive-dimensional coordinate centre;
* an arbitrary globally framed affine linear centre; and
* a polynomial graph centre `Z_i - h_i` over a coefficient domain.

Thus the unresolved geometric bridge is stated without hidden choices:
construct a faithfully flat, typically surjective étale, local model in which
the actual centre ideal pulls back exactly to one of these ideals.  The
algebraic descent of Frobenius heredity is separated from that existence
problem.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalLocalCoordinateModel

noncomputable section

universe u v w x y

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Generic faithfully flat local-model compiler. -/
theorem reflects_of_model
    (p : Nat) (I : Ideal A) (J : Ideal B)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
      (B := B) I = J)
    (hJ : FrobeniusNormalCentre.ReflectsFrobeniusPowers p J) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  apply FrobeniusNormalFaithfullyFlatDescent.reflectsFrobeniusPowers_of_extended
    (B := B) p I
  simpa [hmodel] using hJ

/-- Exact marked heredity compiled from a faithfully flat local model. -/
theorem power_mem_scaled_iff_of_model
    (p : Nat) (I : Ideal A) (J : Ideal B)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
      (B := B) I = J)
    (hJ : FrobeniusNormalCentre.ReflectsFrobeniusPowers p J)
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflects_of_model (B := B) p I J hmodel hJ) e mark x

section PolynomialModels

variable {K : Type w} [Field K]
variable {α : Type x} {ι : Type y}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

variable [Algebra A (P (K := K) (α := α) (ι := ι))]
variable [Module.FaithfullyFlat A (P (K := K) (α := α) (ι := ι))]
variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- A faithfully flat standard coordinate model makes the original centre
Frobenius-normal. -/
theorem reflects_of_coordinateModel
    (I : Ideal A)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := P (K := K) (α := α) (ι := ι)) I =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact reflects_of_model
    (B := P (K := K) (α := α) (ι := ι)) p I
    (CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι)) hmodel
    (FrobeniusNormalCentre.coordinateCentre_reflects
      (K := K) (α := α) (ι := ι) p)

/-- A faithfully flat affine linear-frame model makes the original centre
Frobenius-normal. -/
theorem reflects_of_affineFrameModel
    (I : Ideal A)
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := P (K := K) (α := α) (ι := ι)) I =
      AffineLinearFrameExactFrobeniusHeredity.affineFrameCentreIdeal F b) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact reflects_of_model
    (B := P (K := K) (α := α) (ι := ι)) p I
    (AffineLinearFrameExactFrobeniusHeredity.affineFrameCentreIdeal F b)
    hmodel
    (FrobeniusNormalCentre.affineFrameCentre_reflects p F b)

/-- Exact marked heredity in the base ring from a coordinate model. -/
theorem power_mem_scaled_iff_of_coordinateModel
    (I : Ideal A)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := P (K := K) (α := α) (ι := ι)) I =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι))
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflects_of_coordinateModel
      (K := K) (α := α) (ι := ι) p I hmodel)
    e mark x

end PolynomialModels

section GraphModels

variable {R : Type w} [CommRing R] [IsDomain R]
variable {ι : Type x} [DecidableEq ι]

abbrev GP := MvPolynomial ι R

variable [Algebra A (GP (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (GP (R := R) (ι := ι))]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- A faithfully flat polynomial-graph model makes the original centre
Frobenius-normal. -/
theorem reflects_of_graphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := GP (R := R) (ι := ι)) I =
      PolynomialGraphCentreHeredity.graphIdeal h) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact reflects_of_model
    (B := GP (R := R) (ι := ι)) p I
    (PolynomialGraphCentreHeredity.graphIdeal h) hmodel
    (PolynomialGraphCentreHeredity.graphIdeal_reflectsFrobeniusPowers p h)

/-- Exact marked heredity in the base ring from a polynomial graph model. -/
theorem power_mem_scaled_iff_of_graphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : FrobeniusNormalFaithfullyFlatDescent.extendedIdeal
        (B := GP (R := R) (ι := ι)) I =
      PolynomialGraphCentreHeredity.graphIdeal h)
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflects_of_graphModel (R := R) (ι := ι) p I h hmodel)
    e mark x

end GraphModels

end

end FrobeniusNormalLocalCoordinateModel
end Experimental
end PCRLean
