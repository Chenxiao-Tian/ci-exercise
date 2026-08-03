import Mathlib
import PCRLean.Experimental.FittingLinearSystemAtlas
import PCRLean.Experimental.FittingGraphCentreOverlap
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro
import PCRLean.Experimental.FittingLinearSystemOverlap

/-!
# Row-equivalent Fitting systems have the same graph solution

Exact equality of two localized systems is presentation-dependent.  In
practice, changing a finite equation frame multiplies the matrix and the
right-hand side by the same row-operation matrix.

On every double localization, suppose

`M_d = U_cd M_c`,
`b_d = U_cd b_c`.

No invertibility assumption on `U_cd` is needed: the right-chart matrix `M_d`
is already invertible because its distinguished determinant is a unit.  The
left solution therefore solves the right system, and uniqueness of the right
solution gives equality of the two graph tuples.

Thus compatible row frames automatically produce compatible graph ideals,
Čech-effective global graph coefficients and the complete global affine graph
macro.  This removes a major presentation-dependence from the Fitting-centre
architecture.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemRowCompatibility

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open FittingGraphCentreAtlas
open FittingGraphCentreOverlap
open FittingLinearSystemAtlas

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable (D : FittingLinearSystemAtlas.Data (ι := ι) A)

/-- Left localized coefficient matrix. -/
def leftMatrix (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  (D.matrix c).map (leftMap (A := A) c d)

/-- Right localized coefficient matrix. -/
def rightMatrix (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  (D.matrix d).map (rightMap (A := A) c d)

/-- Left localized right-hand side. -/
def leftRhs (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => leftMap (A := A) c d (D.rhs c i)

/-- Right localized right-hand side. -/
def rightRhs (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => rightMap (A := A) c d (D.rhs d i)

/-- Left localized graph solution. -/
def leftSolution (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => leftMap (A := A) c d (D.graph c i)

/-- Right localized graph solution. -/
def rightSolution (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => rightMap (A := A) c d (D.graph d i)

/-- Row-frame compatibility. -/
structure Compatible : Prop where
  rowTransform : ∀ c d : Chart,
    Matrix ι ι (OverlapRing (A := A) c d)
  matrix_eq : ∀ c d : Chart,
    D.rightMatrix c d = rowTransform c d * D.leftMatrix c d
  rhs_eq : ∀ c d : Chart,
    D.rightRhs c d = (rowTransform c d).mulVec (D.leftRhs c d)

namespace Compatible

variable (H : Compatible D)

/-- The mapped left graph solves the mapped left system. -/
theorem leftSolution_solves_left (c d : Chart) :
    (D.leftMatrix c d).mulVec (D.leftSolution c d) =
      D.leftRhs c d := by
  calc
    (D.leftMatrix c d).mulVec (D.leftSolution c d) =
        fun i => leftMap (A := A) c d
          ((D.matrix c).mulVec (D.graph c) i) := by
      exact FittingLinearSystemOverlap.map_mulVec
        (leftMap (A := A) c d) (D.matrix c) (D.graph c)
    _ = fun i => leftMap (A := A) c d (D.rhs c i) := by
      rw [D.matrix_mulVec_graph c]
    _ = D.leftRhs c d := rfl

/-- The mapped right graph solves the mapped right system. -/
theorem rightSolution_solves_right (c d : Chart) :
    (D.rightMatrix c d).mulVec (D.rightSolution c d) =
      D.rightRhs c d := by
  calc
    (D.rightMatrix c d).mulVec (D.rightSolution c d) =
        fun i => rightMap (A := A) c d
          ((D.matrix d).mulVec (D.graph d) i) := by
      exact FittingLinearSystemOverlap.map_mulVec
        (rightMap (A := A) c d) (D.matrix d) (D.graph d)
    _ = fun i => rightMap (A := A) c d (D.rhs d i) := by
      rw [D.matrix_mulVec_graph d]
    _ = D.rightRhs c d := rfl

/-- Row compatibility makes the left solution a solution of the right system. -/
theorem leftSolution_solves_right (c d : Chart) :
    (D.rightMatrix c d).mulVec (D.leftSolution c d) =
      D.rightRhs c d := by
  rw [H.matrix_eq c d, Matrix.mulVec_mulVec,
    H.leftSolution_solves_left c d, H.rhs_eq c d]

/-- Mapped inverse of the right chart matrix. -/
def rightInverse (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  ((D.matrix d)⁻¹).map (rightMap (A := A) c d)

/-- The mapped inverse is a left inverse of the right overlap matrix. -/
theorem rightInverse_mul_rightMatrix (c d : Chart) :
    H.rightInverse c d * D.rightMatrix c d = 1 := by
  ext i j
  have hlocal : (D.matrix d)⁻¹ * D.matrix d = 1 :=
    Matrix.nonsing_inv_mul (D.matrix d) (D.det_isUnit d)
  have hij := congrArg (rightMap (A := A) c d)
    (congrFun (congrFun hlocal i) j)
  simpa [rightInverse, rightMatrix, Matrix.mul_apply] using hij

/-- The right system has at most one solution. -/
theorem rightMatrix_mulVec_injective (c d : Chart) :
    Function.Injective (D.rightMatrix c d).mulVec := by
  intro x y hxy
  have h := congrArg (H.rightInverse c d).mulVec hxy
  simpa [Matrix.mulVec_mulVec,
    H.rightInverse_mul_rightMatrix c d] using h

/-- Row-equivalent local systems have identical graph solutions on overlap. -/
theorem solution_eq (c d : Chart) :
    D.leftSolution c d = D.rightSolution c d := by
  apply H.rightMatrix_mulVec_injective c d
  rw [H.leftSolution_solves_right c d,
    H.rightSolution_solves_right c d]

/-- Pointwise graph compatibility. -/
theorem graph_eq (c d : Chart) (i : ι) :
    leftMap (A := A) c d (D.graph c i) =
      rightMap (A := A) c d (D.graph d i) :=
  congrFun (H.solution_eq c d) i

/-- Compile row compatibility into the graph compatibility interface. -/
noncomputable def toGraphCompatible :
    FittingGraphCentreOverlap.Compatible D.toGraphAtlasData where
  graph_eq := H.graph_eq

/-- The local centre ideals therefore agree on every overlap. -/
theorem overlapIdeal_eq (c d : Chart) :
    Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (leftMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph c)) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (rightMap (A := A) c d))
        (PolynomialGraphCentreHeredity.graphIdeal (D.graph d)) :=
  H.toGraphCompatible.overlapIdeal_eq c d

/-- The row-compatible systems glue to one actual global graph tuple. -/
noncomputable def globalGraph : ι → R :=
  H.toGraphCompatible.toCompatibleSectionData.globalGraph

/-- Every local graph is the localization of the global graph. -/
theorem globalGraph_localizes (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c) (H.globalGraph i) =
      D.graph c i :=
  H.toGraphCompatible.globalGraph_localizes c i

/-- Every local system ideal is the base change of the global graph centre. -/
theorem localEquationIdeal_is_globalCentreBaseChange (c : Chart) :
    (D.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal H.globalGraph) := by
  rw [D.equationIdeal_eq_graphIdeal c]
  exact H.toGraphCompatible.local_centre_is_global_baseChange c

end Compatible

end

end FittingLinearSystemRowCompatibility
end Experimental
end PCRLean
