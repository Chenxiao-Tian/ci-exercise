import Mathlib
import PCRLean.Experimental.FittingLinearSystemAtlas
import PCRLean.Experimental.FittingGraphCentreOverlap
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro

/-!
# Compatible Fitting linear systems have compatible graph solutions

On two determinant charts, map the coefficient matrices and right-hand sides to
the canonical double localization.  If the mapped systems agree, their graph
solutions agree automatically: the common coefficient matrix is invertible,
so a common affine linear system has a unique solution.

This removes graph compatibility as an independent hypothesis.  Compatibility
of the finite linear systems produced by a common Frobenius/Hasse/Fitting core
is enough to obtain:

* compatible local graph tuples;
* compatible actual centre ideals;
* Čech-effective global graph coefficients;
* one global actual graph centre; and
* the complete global affine graph resolution macro.

The remaining universal bridge is therefore sharply localized: extract one
finite determinant-normalized system atlas from an arbitrary core and prove
its matrices and right-hand sides agree after double localization.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemOverlap

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

/-- Ring maps commute with matrix-vector multiplication. -/
theorem map_mulVec
    {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (M : Matrix ι ι S) (x : ι → S) :
    (M.map f).mulVec (fun i => f (x i)) =
      fun i => f (M.mulVec x i) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- System data agrees on every double-localization overlap. -/
structure Compatible : Prop where
  matrix_eq : ∀ c d : Chart,
    (D.matrix c).map (leftMap (A := A) c d) =
      (D.matrix d).map (rightMap (A := A) c d)
  rhs_eq : ∀ c d : Chart, ∀ i : ι,
    leftMap (A := A) c d (D.rhs c i) =
      rightMap (A := A) c d (D.rhs d i)

namespace Compatible

variable (H : Compatible D)

/-- Common overlap matrix, represented from the left chart. -/
def commonMatrix (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  (D.matrix c).map (leftMap (A := A) c d)

/-- Common overlap right-hand side. -/
def commonRhs (c d : Chart) :
    ι → OverlapRing (A := A) c d :=
  fun i => leftMap (A := A) c d (D.rhs c i)

/-- Left-chart solution mapped to the overlap. -/
def leftSolution (c d : Chart) :
    ι → OverlapRing (A := A) c d :=
  fun i => leftMap (A := A) c d (D.graph c i)

/-- Right-chart solution mapped to the overlap. -/
def rightSolution (c d : Chart) :
    ι → OverlapRing (A := A) c d :=
  fun i => rightMap (A := A) c d (D.graph d i)

/-- The mapped inverse matrix from the left chart. -/
def commonInverse (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  ((D.matrix c)⁻¹).map (leftMap (A := A) c d)

/-- The mapped inverse is a left inverse of the common overlap matrix. -/
theorem commonInverse_mul_commonMatrix (c d : Chart) :
    H.commonInverse c d * H.commonMatrix c d = 1 := by
  ext i j
  have hlocal : (D.matrix c)⁻¹ * D.matrix c = 1 :=
    Matrix.nonsing_inv_mul (D.matrix c) (D.det_isUnit c)
  have hij := congrArg (leftMap (A := A) c d)
    (congrFun (congrFun hlocal i) j)
  simpa [commonInverse, commonMatrix, Matrix.mul_apply] using hij

/-- Multiplication by the common overlap matrix is injective. -/
theorem commonMatrix_mulVec_injective (c d : Chart) :
    Function.Injective (H.commonMatrix c d).mulVec := by
  intro x y hxy
  have h := congrArg (H.commonInverse c d).mulVec hxy
  simpa [Matrix.mulVec_mulVec,
    H.commonInverse_mul_commonMatrix c d] using h

/-- The left local graph solves the common overlap system. -/
theorem leftSolution_solves (c d : Chart) :
    (H.commonMatrix c d).mulVec (H.leftSolution c d) =
      H.commonRhs c d := by
  calc
    (H.commonMatrix c d).mulVec (H.leftSolution c d) =
        fun i => leftMap (A := A) c d
          ((D.matrix c).mulVec (D.graph c) i) := by
      exact map_mulVec
        (leftMap (A := A) c d) (D.matrix c) (D.graph c)
    _ = fun i => leftMap (A := A) c d (D.rhs c i) := by
      rw [D.matrix_mulVec_graph c]
    _ = H.commonRhs c d := rfl

/-- The right local graph solves the same common overlap system. -/
theorem rightSolution_solves (c d : Chart) :
    (H.commonMatrix c d).mulVec (H.rightSolution c d) =
      H.commonRhs c d := by
  rw [H.matrix_eq c d]
  calc
    ((D.matrix d).map (rightMap (A := A) c d)).mulVec
        (H.rightSolution c d) =
        fun i => rightMap (A := A) c d
          ((D.matrix d).mulVec (D.graph d) i) := by
      exact map_mulVec
        (rightMap (A := A) c d) (D.matrix d) (D.graph d)
    _ = fun i => rightMap (A := A) c d (D.rhs d i) := by
      rw [D.matrix_mulVec_graph d]
    _ = H.commonRhs c d := by
      funext i
      exact (H.rhs_eq c d i).symm

/-- Uniqueness of solutions gives equality of graph tuples on the overlap. -/
theorem solution_eq (c d : Chart) :
    H.leftSolution c d = H.rightSolution c d := by
  apply H.commonMatrix_mulVec_injective c d
  rw [H.leftSolution_solves c d, H.rightSolution_solves c d]

/-- Pointwise graph compatibility. -/
theorem graph_eq (c d : Chart) (i : ι) :
    leftMap (A := A) c d (D.graph c i) =
      rightMap (A := A) c d (D.graph d i) := by
  exact congrFun (H.solution_eq c d) i

/-- Compile compatible systems into the graph-compatibility interface. -/
noncomputable def toGraphCompatible :
    FittingGraphCentreOverlap.Compatible D.toGraphAtlasData where
  graph_eq := H.graph_eq

/-- Hence all local graph ideals agree on every overlap. -/
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

/-- Compatible finite systems therefore produce one actual global graph tuple. -/
noncomputable def globalGraph : ι → R :=
  H.toGraphCompatible.toCompatibleSectionData.globalGraph

/-- Every local solution is the localization of the global solution. -/
theorem globalGraph_localizes (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c) (H.globalGraph i) =
      D.graph c i :=
  H.toGraphCompatible.globalGraph_localizes c i

/-- Every local system ideal is the base change of one actual global graph
centre ideal. -/
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

end FittingLinearSystemOverlap
end Experimental
end PCRLean
