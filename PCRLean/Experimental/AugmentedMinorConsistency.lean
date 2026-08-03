import Mathlib
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Augmented-minor consistency via the Schur complement

Let `A` be an invertible square coefficient matrix, `b` a selected right-hand
side, `a` one additional equation row and `r` its right-hand side.  Form the
augmented block matrix

`[ A  b ]`
`[ a  r ]`.

The Schur-complement determinant formula gives

`det(augmented) = det(A) * (r - a · A⁻¹ b)`.

Since `det(A)` is a unit, vanishing of the augmented determinant is equivalent
to the selected solution `A⁻¹ b` satisfying the additional equation.

This is the determinantal consistency bridge needed for a maximal-rank Fitting
atlas.  It turns vanishing of augmented minors into full-packet consistency,
which then forces all selected-minor graph solutions to agree on overlaps.
-/

namespace PCRLean
namespace Experimental
namespace AugmentedMinorConsistency

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Column block associated to a vector. -/
def column (b : ι → R) : Matrix ι Unit R :=
  fun i _ => b i

/-- Row block associated to a covector. -/
def row (a : ι → R) : Matrix Unit ι R :=
  fun _ j => a j

/-- One-by-one scalar block. -/
def scalar (r : R) : Matrix Unit Unit R :=
  fun _ _ => r

/-- The selected system with one additional augmented equation. -/
def augmented
    (A : Matrix ι ι R) (b a : ι → R) (r : R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks A (column b) (row a) (scalar r)

/-- Selected-system solution. -/
def solution (A : Matrix ι ι R) (b : ι → R) : ι → R :=
  A⁻¹.mulVec b

/-- The scalar Schur complement is the equation residual. -/
theorem schurComplement_entry
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    [Invertible A] :
    (scalar r - row a * ⅟A * column b) () () =
      r - dotProduct a ((⅟A).mulVec b) := by
  simp [scalar, row, column, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Determinant of the one-by-one Schur complement. -/
theorem det_schurComplement
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    [Invertible A] :
    (scalar r - row a * ⅟A * column b).det =
      r - dotProduct a ((⅟A).mulVec b) := by
  simp [scalar, row, column, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Exact Schur determinant formula for one additional equation. -/
theorem det_augmented
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    [Invertible A] :
    (augmented A b a r).det =
      A.det * (r - dotProduct a ((⅟A).mulVec b)) := by
  rw [augmented, Matrix.det_fromBlocks₁₁]
  rw [det_schurComplement]

/-- Vanishing of the augmented minor forces the selected solution to satisfy
the additional equation. -/
theorem equation_of_det_augmented_eq_zero
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    (hdet : IsUnit A.det)
    (haug : (augmented A b a r).det = 0) :
    dotProduct a (solution A b) = r := by
  letI : Invertible A.det := Classical.choice hdet.nonempty_invertible
  letI : Invertible A := Matrix.invertibleOfDetInvertible A
  have hformula := det_augmented A b a r
  have hprod : A.det * (r - dotProduct a ((⅟A).mulVec b)) = 0 := by
    rw [← hformula, haug]
  have hres : r - dotProduct a ((⅟A).mulVec b) = 0 := by
    have h := congrArg (fun z : R => ⅟(A.det) * z) hprod
    simpa [mul_assoc] using h
  have hEq : r = dotProduct a ((⅟A).mulVec b) :=
    sub_eq_zero.mp hres
  rw [solution, ← Matrix.invOf_eq_nonsing_inv A]
  exact hEq.symm

/-- Conversely, a satisfied additional equation makes the augmented minor
vanish. -/
theorem det_augmented_eq_zero_of_equation
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    (hdet : IsUnit A.det)
    (heq : dotProduct a (solution A b) = r) :
    (augmented A b a r).det = 0 := by
  letI : Invertible A.det := Classical.choice hdet.nonempty_invertible
  letI : Invertible A := Matrix.invertibleOfDetInvertible A
  rw [det_augmented]
  have heq' : dotProduct a ((⅟A).mulVec b) = r := by
    simpa [solution, Matrix.invOf_eq_nonsing_inv A] using heq
  rw [heq', sub_self, mul_zero]

/-- Exact equivalence between augmented-minor vanishing and consistency. -/
theorem det_augmented_eq_zero_iff
    (A : Matrix ι ι R) (b a : ι → R) (r : R)
    (hdet : IsUnit A.det) :
    (augmented A b a r).det = 0 ↔
      dotProduct a (solution A b) = r := by
  constructor
  · exact equation_of_det_augmented_eq_zero A b a r hdet
  · exact det_augmented_eq_zero_of_equation A b a r hdet

end

end AugmentedMinorConsistency
end Experimental
end PCRLean
