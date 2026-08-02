import Mathlib

/-!
# Fixed finite jets do not determine deeper terms

For every cutoff `L` and every exponent `q > L`, the zero polynomial and
`X^q` have identical coefficients in all degrees at most `L`, but they are
different polynomials.  This is the exact algebraic no-go behind the repeated
warning that one frozen finite jet cannot predict arbitrarily deep future
Frobenius or contact data.
-/

namespace PCRLean.NoGo.FiniteJetBlindness

open Polynomial

variable {R : Type*} [Semiring R]

/-- A monomial of degree `q` is invisible in every strictly lower coefficient. -/
theorem X_pow_coeff_zero_below {m q : ℕ} (h : m < q) :
    coeff (X ^ q : R[X]) m = 0 := by
  rw [coeff_X_pow]
  simp [h.ne]

/-- The zero polynomial and `X^q` have the same jet through degree `L` when
`q` lies above the cutoff. -/
theorem zero_and_X_pow_agree_below
    {L q : ℕ} (hLq : L < q) :
    ∀ m ≤ L, coeff (0 : R[X]) m = coeff (X ^ q : R[X]) m := by
  intro m hm
  have hmq : m < q := lt_of_le_of_lt hm hLq
  simp [X_pow_coeff_zero_below hmq]

variable [Nontrivial R]

/-- The invisible high monomial is nevertheless nonzero. -/
theorem X_pow_ne_zero (q : ℕ) : (X ^ q : R[X]) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : R[X] => coeff f q) hzero
  simpa using hcoeff

/-- No fixed coefficient cutoff is faithful on all polynomials. -/
theorem fixed_cutoff_not_faithful (L q : ℕ) (hLq : L < q) :
    (∀ m ≤ L, coeff (0 : R[X]) m = coeff (X ^ q : R[X]) m) ∧
      (0 : R[X]) ≠ X ^ q := by
  constructor
  · exact zero_and_X_pow_agree_below hLq
  · exact (X_pow_ne_zero q).symm

end PCRLean.NoGo.FiniteJetBlindness
