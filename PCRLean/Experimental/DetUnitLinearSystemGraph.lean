import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PCRLean.Experimental.InvertibleLinearSystemGraph

/-!
# Determinant-unit linear systems define polynomial graph centres

For a square matrix `M` with unit determinant, mathlib's nonsingular inverse
provides a canonical two-sided inverse. Therefore every affine linear system

`M Z = b`

compiles directly to the graph

`Z = M⁻¹ b`.

The actual equation ideal is proved equal to the actual graph ideal. No inverse
matrix or graph tuple has to be supplied as extra geometric data once the
Fitting determinant is a unit.
-/

namespace PCRLean
namespace Experimental
namespace DetUnitLinearSystemGraph

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Affine square system with a determinant-unit coefficient matrix. -/
structure System where
  matrix : Matrix ι ι R
  rhs : ι → R
  det_isUnit : IsUnit matrix.det

namespace System

variable (S : System (R := R) (ι := ι))

/-- Canonical explicit-inverse system. -/
noncomputable def toInvertibleSystem :
    InvertibleLinearSystemGraph.System (R := R) (ι := ι) where
  matrix := S.matrix
  inverse := S.matrix⁻¹
  rhs := S.rhs
  leftInverse := Matrix.mul_nonsing_inv S.matrix S.det_isUnit
  rightInverse := Matrix.nonsing_inv_mul S.matrix S.det_isUnit

/-- Canonical graph solution. -/
noncomputable def solution : ι → R :=
  S.matrix⁻¹.mulVec S.rhs

/-- The canonical solution satisfies the original system. -/
theorem matrix_mulVec_solution :
    S.matrix.mulVec S.solution = S.rhs := by
  simpa [solution, toInvertibleSystem] using
    S.toInvertibleSystem.matrix_mulVec_solution

/-- Pointwise form of the solution equation. -/
theorem matrix_mulVec_solution_apply (i : ι) :
    S.matrix.mulVec S.solution i = S.rhs i := by
  rw [S.matrix_mulVec_solution]

/-- Actual system-equation ideal. -/
noncomputable def equationIdeal : Ideal (MvPolynomial ι R) :=
  S.toInvertibleSystem.equationIdeal

/-- Main determinant-unit bridge. -/
theorem equationIdeal_eq_graphIdeal :
    S.equationIdeal =
      PolynomialGraphCentreHeredity.graphIdeal S.solution := by
  exact S.toInvertibleSystem.equationIdeal_eq_graphIdeal

/-- Exact quotient by the determinant-unit system. -/
noncomputable def quotientEquiv :
    (MvPolynomial ι R ⧸ S.equationIdeal) ≃+* R := by
  rw [S.equationIdeal_eq_graphIdeal]
  exact PolynomialGraphCentreQuotient.quotientEquiv S.solution

/-- Determinant-unit local data therefore yields the full graph-centre
certificate whenever the coefficient ring is Noetherian regular. -/
noncomputable def centreCertificate
    [IsDomain R] [IsNoetherianRing R] [IsRegularRing R]
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p S.solution e :=
  PolynomialGraphFrobeniusCentreCertificate.certificate
    p S.solution e

end System

end

end DetUnitLinearSystemGraph
end Experimental
end PCRLean
