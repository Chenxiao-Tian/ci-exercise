import Mathlib
import Mathlib.RingTheory.Localization.Away.Basic
import PCRLean.Experimental.FittingGraphCentreAtlas
import PCRLean.Experimental.PolynomialGraphBaseChange

/-!
# Pairwise overlap gluing for a Fitting graph-centre atlas

For determinant charts `D(d_c)` and `D(d_d)`, use the canonical overlap

`D(d_c d_d) = D(d_c) ∩ D(d_d)`.

There are canonical localization maps from both chart rings to the overlap
ring. If the two graph tuples have the same image there, exact base change of
graph ideals implies that the two actual local centre ideals have identical
extensions to the overlap.

This is the affine pairwise descent condition required for a coherent centre
sheaf. The chosen order `d_c*d_d` matches `PrimeSpectrum.basicOpen_mul`
exactly, which allows the next module to compare these maps to structure-sheaf
restriction maps without a commutativity transport.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphCentreOverlap

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open FittingGraphCentreAtlas

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}

/-- Canonical double-localization overlap, ordered exactly as the intersection
`D(d_c) ∩ D(d_d)`. -/
abbrev OverlapRing (c d : Chart) :=
  Localization.Away (A.determinant c * A.determinant d)

/-- Map from the first determinant chart to the overlap. -/
noncomputable def leftMap (c d : Chart) :
    ChartRing A c →+* OverlapRing (A := A) c d :=
  IsLocalization.Away.awayToAwayRight
    (S := ChartRing A c)
    (P := OverlapRing (A := A) c d)
    (A.determinant c) (A.determinant d)

/-- Map from the second determinant chart to the same overlap. -/
noncomputable def rightMap (c d : Chart) :
    ChartRing A d →+* OverlapRing (A := A) c d :=
  IsLocalization.Away.awayToAwayLeft
    (S := ChartRing A d)
    (P := OverlapRing (A := A) c d)
    (A.determinant d) (A.determinant c)

@[simp] theorem leftMap_algebraMap
    (c d : Chart) (r : R) :
    leftMap (A := A) c d (algebraMap R (ChartRing A c) r) =
      algebraMap R (OverlapRing (A := A) c d) r := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := ChartRing A c)
    (P := OverlapRing (A := A) c d)
    (A.determinant c) (A.determinant d) r

@[simp] theorem rightMap_algebraMap
    (c d : Chart) (r : R) :
    rightMap (A := A) c d (algebraMap R (ChartRing A d) r) =
      algebraMap R (OverlapRing (A := A) c d) r := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := ChartRing A d)
    (P := OverlapRing (A := A) c d)
    (A.determinant d) (A.determinant c) r

/-- Pointwise equality of local graph presentations on every overlap. -/
structure Compatible
    (D : GraphAtlasData (ι := ι) A) : Prop where
  graph_eq : ∀ c d i,
    leftMap (A := A) c d (D.graph c i) =
      rightMap (A := A) c d (D.graph d i)

namespace Compatible

variable {D : GraphAtlasData (ι := ι) A}
    (H : Compatible D)

/-- The two local graph ideals extend to exactly the same actual ideal on the
overlap. -/
theorem overlapIdeal_eq (c d : Chart) :
    Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (leftMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph c)) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (rightMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph d)) := by
  rw [PolynomialGraphBaseChange.map_graphIdeal_eq,
    PolynomialGraphBaseChange.map_graphIdeal_eq]
  apply congrArg PolynomialGraphCentreHeredity.graphIdeal
  funext i
  exact H.graph_eq c d i

/-- Pairwise actual-ideal descent certificate for the whole finite atlas. -/
structure Certificate where
  overlapEquality : ∀ c d : Chart,
    Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (leftMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph c)) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (rightMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph d))

/-- Assemble all pairwise overlap equalities. -/
noncomputable def certificate : Certificate H where
  overlapEquality := H.overlapIdeal_eq

end Compatible

end

end FittingGraphCentreOverlap
end Experimental
end PCRLean
