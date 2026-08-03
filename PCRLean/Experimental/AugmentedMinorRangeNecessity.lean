import Mathlib
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import PCRLean.Experimental.AugmentedMinorConsistency

/-!
# Augmented minors vanish for every actual solution

The earlier Schur-complement compiler proves that, on an invertible selected
minor, vanishing of an augmented determinant is equivalent to satisfaction of
one additional equation.  The converse direction needed for a global range
criterion does not require any selected minor to be invertible.

If `A z = b` and `a · z = r`, then the last column of

`[ A  b ]`
`[ a  r ]`

is a linear combination of the preceding columns.  We formalize this by right
multiplying by the determinant-one block matrix

`[ 1  -z ]`
`[ 0   1 ]`.

The last column becomes zero, so the augmented determinant vanishes over an
arbitrary commutative ring.  This supplies the necessity half of the maximal
minor range criterion without localization or rank assumptions.
-/

namespace PCRLean
namespace Experimental
namespace AugmentedMinorRangeNecessity

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

open AugmentedMinorConsistency

/-- Determinant-one column operation subtracting the vector `z` from the last
column. -/
def eliminateLastColumn (z : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks
    (1 : Matrix ι ι R)
    (column (-z))
    (0 : Matrix Unit ι R)
    (1 : Matrix Unit Unit R)

/-- The elimination matrix has determinant one. -/
theorem det_eliminateLastColumn (z : ι → R) :
    (eliminateLastColumn z).det = 1 := by
  rw [eliminateLastColumn, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- Block matrix with the same first columns as the augmented system and zero
last column. -/
def zeroLastColumn
    (A : Matrix ι ι R) (a : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks
    A
    (0 : Matrix ι Unit R)
    (row a)
    (0 : Matrix Unit Unit R)

/-- A block matrix with zero final column has zero determinant. -/
theorem det_zeroLastColumn
    (A : Matrix ι ι R) (a : ι → R) :
    (zeroLastColumn A a).det = 0 := by
  rw [zeroLastColumn, Matrix.det_fromBlocks_zero₁₂]
  simp

/-- Exact elimination identity when the displayed vector solves all equations. -/
theorem augmented_mul_eliminateLastColumn
    (A : Matrix ι ι R) (b a z : ι → R) (r : R)
    (hselected : A.mulVec z = b)
    (hextra : dotProduct a z = r) :
    augmented A b a r * eliminateLastColumn z =
      zeroLastColumn A a := by
  rw [augmented, eliminateLastColumn, zeroLastColumn,
    Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · ext i u
    have hi := congrFun hselected i
    simp only [Matrix.mulVec, dotProduct] at hi
    simp [column, Matrix.mul_apply, hi]
  · simp
  · ext u v
    simp [row, column, scalar, Matrix.mul_apply, dotProduct, hextra]

/-- Every actual solution forces the corresponding augmented determinant to
vanish, without an invertibility hypothesis on the selected matrix. -/
theorem det_augmented_eq_zero_of_solution
    (A : Matrix ι ι R) (b a z : ι → R) (r : R)
    (hselected : A.mulVec z = b)
    (hextra : dotProduct a z = r) :
    (augmented A b a r).det = 0 := by
  have hmatrix := augmented_mul_eliminateLastColumn
    A b a z r hselected hextra
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul, det_eliminateLastColumn,
    det_zeroLastColumn, mul_one] at hdet
  exact hdet

end

end AugmentedMinorRangeNecessity
end Experimental
end PCRLean
