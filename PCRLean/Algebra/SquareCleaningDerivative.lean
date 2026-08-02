import Mathlib
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Differential invariance under square cleaning

In characteristic two the derivative of a square vanishes.  Consequently the
ordinary Jacobian datum of a univariate radicial coefficient is invariant under
cleaning by adding a square.  This is the first formal seed of the cleaning-
stable differential packet used by the PCR program.
-/

namespace PCRLean.Algebra.SquareCleaningDerivative

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The derivative of a polynomial square vanishes in characteristic two. -/
@[simp] theorem derivative_square (g : R[X]) :
    derivative (g ^ 2) = 0 := by
  rw [pow_two, derivative_mul]
  rw [mul_comm g (derivative g)]
  exact CharTwo.add_self_eq_zero (derivative g * g)

/-- Adding a square cleaner does not change the derivative. -/
@[simp] theorem derivative_add_square (f g : R[X]) :
    derivative (f + g ^ 2) = derivative f := by
  rw [derivative_add, derivative_square, add_zero]

/-- Two cleaned representatives have the same derivative whenever they differ
by a square. -/
theorem derivative_eq_of_eq_add_square {f f' g : R[X]}
    (h : f' = f + g ^ 2) :
    derivative f' = derivative f := by
  rw [h, derivative_add_square]

/-- The principal Jacobian ideal is invariant under square cleaning. -/
theorem jacobian_span_invariant (f g : R[X]) :
    Ideal.span ({derivative (f + g ^ 2)} : Set R[X]) =
      Ideal.span ({derivative f} : Set R[X]) := by
  rw [derivative_add_square]

end PCRLean.Algebra.SquareCleaningDerivative
