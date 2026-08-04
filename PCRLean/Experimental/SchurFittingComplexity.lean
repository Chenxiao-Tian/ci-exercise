import Mathlib

/-!
# Strict complexity descent for Schur--Fitting residual packets

On a determinant chart with an invertible `r × r` pivot block, elementary
block operations reduce a presentation matrix to an identity block plus its
Schur complement.  The remaining presentation has shape

`(rows - r) × (cols - r)`.

Whenever `r > 0`, the sum of the two dimensions strictly decreases.  This
arithmetic leaf is the well-foundedness certificate for the positive-pivot
part of the proposed Fitting recursion.  The algebraic Schur-complement
cokernel equivalence and the rank-zero geometric exit remain separate nodes.
-/

namespace PCRLean
namespace Experimental
namespace SchurFittingComplexity

structure MatrixShape where
  rows : Nat
  cols : Nat
  deriving DecidableEq, Repr

namespace MatrixShape

/-- Additive presentation-size rank. -/
def complexity (s : MatrixShape) : Nat :=
  s.rows + s.cols

/-- Shape of the Schur residual after removing an `r × r` pivot block. -/
def residual (s : MatrixShape) (r : Nat) : MatrixShape where
  rows := s.rows - r
  cols := s.cols - r

/-- Every positive legal pivot strictly lowers the presentation-size rank. -/
theorem residual_complexity_lt
    (s : MatrixShape) (r : Nat)
    (hr : 0 < r) (hrows : r ≤ s.rows) (hcols : r ≤ s.cols) :
    (s.residual r).complexity < s.complexity := by
  simp [complexity, residual]
  omega

/-- In particular the residual shape cannot equal the original shape. -/
theorem residual_ne_self
    (s : MatrixShape) (r : Nat)
    (hr : 0 < r) (hrows : r ≤ s.rows) (hcols : r ≤ s.cols) :
    s.residual r ≠ s := by
  intro h
  have hlt := residual_complexity_lt s r hr hrows hcols
  rw [h] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Any chain of positive legal Schur reductions is well founded when oriented
by `complexity`. -/
theorem residual_relation_wellFounded :
    WellFounded
      (fun a b : MatrixShape => a.complexity < b.complexity) := by
  exact WellFounded.onFun Nat.lt_wfRel.wf MatrixShape.complexity

end MatrixShape

end SchurFittingComplexity
end Experimental
end PCRLean
