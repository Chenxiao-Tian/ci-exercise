import Mathlib
import PCRLean.Experimental.FittingLinearSystemAtlas
import PCRLean.Experimental.FittingGraphCentreOverlap
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro
import PCRLean.Experimental.FittingLinearSystemOverlap

/-!
# Fitting systems selected from one common finite equation packet

Let a finite affine linear packet over `R` be

`M z = b`,

where rows are indexed by `κ` and unknown normal coordinates by `ι`.  A
Fitting chart chooses `ι` rows whose square determinant is the distinguished
minor.  After localizing away from that minor, the selected subsystem has a
unique graph solution.

Different charts need not use the same rows or be related by an explicitly
supplied row transformation.  It is enough that each selected solution satisfies
*all* rows of the common packet.  Then the solution from chart `c` satisfies
the selected equations of chart `d`; uniqueness on chart `d` forces the two
solutions to agree on the double localization.

Thus a common finite packet plus local consistency automatically yields graph
overlap compatibility, one actual global graph centre and the complete global
affine graph macro.

The next exact bridge is the determinantal consistency theorem: on the maximal
rank locus, vanishing of the augmented `(r+1)`-minors of `[M|b]` should imply
that every selected-minor solution satisfies the full packet.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemCommonPacket

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type x} [Fintype κ]

open FittingGraphCentreAtlas
open FittingGraphCentreOverlap
open FittingLinearSystemAtlas

variable (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))

/-- One common finite affine linear equation packet and a square row selection
on every determinant chart. -/
structure Data where
  matrix : Matrix κ ι R
  rhs : κ → R
  selectedRow : Chart → ι → κ
  det_eq : ∀ c : Chart,
    (Matrix.of fun i j =>
      algebraMap R (ChartRing A c)
        (matrix (selectedRow c i) j)).det =
      algebraMap R (ChartRing A c) (A.determinant c)

namespace Data

variable (D : Data (ι := ι) A)

/-- Selected square matrix on one chart. -/
def localMatrix (c : Chart) :
    Matrix ι ι (ChartRing A c) :=
  Matrix.of fun i j =>
    algebraMap R (ChartRing A c)
      (D.matrix (D.selectedRow c i) j)

/-- Selected right-hand side. -/
def localRhs (c : Chart) : ι → ChartRing A c :=
  fun i => algebraMap R (ChartRing A c)
    (D.rhs (D.selectedRow c i))

/-- Determinant normalization for the selected subsystem. -/
theorem localMatrix_det_eq (c : Chart) :
    (D.localMatrix c).det =
      algebraMap R (ChartRing A c) (A.determinant c) := by
  exact D.det_eq c

/-- Derived determinant-normalized system atlas. -/
noncomputable def toSystemAtlas :
    FittingLinearSystemAtlas.Data (ι := ι) A where
  matrix := D.localMatrix
  rhs := D.localRhs
  det_eq := D.localMatrix_det_eq

/-- Local graph solution. -/
noncomputable def graph (c : Chart) : ι → ChartRing A c :=
  D.toSystemAtlas.graph c

/-- Full packet equation evaluated on a chart solution. -/
def fullEquationValue (c : Chart) (r : κ) : ChartRing A c :=
  ∑ j : ι,
    algebraMap R (ChartRing A c) (D.matrix r j) * D.graph c j

/-- Local consistency: every selected-minor solution satisfies every equation
of the common packet. -/
structure Consistent : Prop where
  fullEquation : ∀ c : Chart, ∀ r : κ,
    D.fullEquationValue c r =
      algebraMap R (ChartRing A c) (D.rhs r)

namespace Consistent

variable (H : D.Consistent)

/-- Left chart graph mapped to one overlap. -/
def leftSolution (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => leftMap (A := A) c d (D.graph c i)

/-- Right chart graph mapped to one overlap. -/
def rightSolution (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => rightMap (A := A) c d (D.graph d i)

/-- Right selected matrix mapped to the overlap. -/
def rightMatrix (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  (D.localMatrix d).map (rightMap (A := A) c d)

/-- Right selected right-hand side mapped to the overlap. -/
def rightRhs (c d : Chart) : ι → OverlapRing (A := A) c d :=
  fun i => rightMap (A := A) c d (D.localRhs d i)

/-- The right local graph solves the right selected overlap system. -/
theorem rightSolution_solves (c d : Chart) :
    (H.rightMatrix c d).mulVec (H.rightSolution c d) =
      H.rightRhs c d := by
  calc
    (H.rightMatrix c d).mulVec (H.rightSolution c d) =
        fun i => rightMap (A := A) c d
          ((D.localMatrix d).mulVec (D.graph d) i) := by
      exact FittingLinearSystemOverlap.map_mulVec
        (rightMap (A := A) c d) (D.localMatrix d) (D.graph d)
    _ = fun i => rightMap (A := A) c d (D.localRhs d i) := by
      rw [D.toSystemAtlas.matrix_mulVec_graph d]
    _ = H.rightRhs c d := rfl

/-- The left graph satisfies the selected equations of the right chart because
it satisfies the complete common packet. -/
theorem leftSolution_solves_right (c d : Chart) :
    (H.rightMatrix c d).mulVec (H.leftSolution c d) =
      H.rightRhs c d := by
  funext i
  have hfull := congrArg (leftMap (A := A) c d)
    (H.fullEquation c (D.selectedRow d i))
  simpa [rightMatrix, rightRhs, leftSolution, localMatrix, localRhs,
    fullEquationValue, Matrix.mulVec, dotProduct] using hfull

/-- Mapped inverse of the right selected matrix. -/
def rightInverse (c d : Chart) :
    Matrix ι ι (OverlapRing (A := A) c d) :=
  ((D.localMatrix d)⁻¹).map (rightMap (A := A) c d)

/-- The mapped inverse is a left inverse. -/
theorem rightInverse_mul_rightMatrix (c d : Chart) :
    H.rightInverse c d * H.rightMatrix c d = 1 := by
  ext i j
  have hlocal : (D.localMatrix d)⁻¹ * D.localMatrix d = 1 :=
    Matrix.nonsing_inv_mul (D.localMatrix d)
      (D.toSystemAtlas.det_isUnit d)
  have hij := congrArg (rightMap (A := A) c d)
    (congrFun (congrFun hlocal i) j)
  simpa [rightInverse, rightMatrix, Matrix.mul_apply] using hij

/-- The right selected system has a unique solution. -/
theorem rightMatrix_mulVec_injective (c d : Chart) :
    Function.Injective (H.rightMatrix c d).mulVec := by
  intro x y hxy
  have h := congrArg (H.rightInverse c d).mulVec hxy
  simpa [Matrix.mulVec_mulVec,
    H.rightInverse_mul_rightMatrix c d] using h

/-- All selected-minor graph solutions agree on overlaps. -/
theorem solution_eq (c d : Chart) :
    H.leftSolution c d = H.rightSolution c d := by
  apply H.rightMatrix_mulVec_injective c d
  rw [H.leftSolution_solves_right c d,
    H.rightSolution_solves c d]

/-- Pointwise graph compatibility. -/
theorem graph_eq (c d : Chart) (i : ι) :
    leftMap (A := A) c d (D.graph c i) =
      rightMap (A := A) c d (D.graph d i) :=
  congrFun (H.solution_eq c d) i

/-- Compile common-packet consistency to graph compatibility. -/
noncomputable def toGraphCompatible :
    FittingGraphCentreOverlap.Compatible
      D.toSystemAtlas.toGraphAtlasData where
  graph_eq := H.graph_eq

/-- Compatible local graphs glue to an actual global graph tuple. -/
noncomputable def globalGraph : ι → R :=
  H.toGraphCompatible.toCompatibleSectionData.globalGraph

/-- Every local graph is the localization of the global graph. -/
theorem globalGraph_localizes (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c) (H.globalGraph i) =
      D.graph c i :=
  H.toGraphCompatible.globalGraph_localizes c i

/-- Every selected subsystem ideal is the base change of one global graph
centre. -/
theorem localEquationIdeal_is_globalCentreBaseChange (c : Chart) :
    (D.toSystemAtlas.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal H.globalGraph) := by
  rw [D.toSystemAtlas.equationIdeal_eq_graphIdeal c]
  exact H.toGraphCompatible.local_centre_is_global_baseChange c

end Consistent

end Data

end

end FittingLinearSystemCommonPacket
end Experimental
end PCRLean
