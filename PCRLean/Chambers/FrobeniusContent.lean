import Mathlib

/-!
# Frobenius-content recurrence

This file formalizes the algebraic core of the principal anchored
Frobenius-content word.  No Frobenius additivity is used: only the exact
monomial factorization after the ordinary blowup of the coordinate centre.
-/

namespace PCRLean.Chambers.FrobeniusContent

variable {R : Type*} [CommRing R]

/-- In the `t`-pivot chart, the content depth drops from `n+1` to `n`. -/
theorem active_factorization (t Y U : R) (q n : ℕ) :
    (t * Y) ^ q + t ^ ((n + 1) * q) * U =
      t ^ q * (Y ^ q + t ^ (n * q) * U) := by
  have hexp : (n + 1) * q = q + n * q := by
    calc
      (n + 1) * q = n * q + q := by simp [Nat.add_mul]
      _ = q + n * q := Nat.add_comm _ _
  rw [mul_pow, hexp, pow_add]
  ring

/-- In the sibling `y`-pivot chart, the exceptional factor is `y^q`. -/
theorem sibling_factorization (y T U : R) (q n : ℕ) :
    y ^ q + (y * T) ^ ((n + 1) * q) * U =
      y ^ q * (1 + y ^ (n * q) * T ^ ((n + 1) * q) * U) := by
  have hexp : (n + 1) * q = q + n * q := by
    calc
      (n + 1) * q = n * q + q := by simp [Nat.add_mul]
      _ = q + n * q := Nat.add_comm _ _
  rw [mul_pow, hexp, pow_add]
  ring

/-- With positive Frobenius weight and positive remaining depth, the sibling
controlled transform restricts to the unit on the exceptional divisor. -/
@[simp] theorem sibling_exceptional_value_of_pos
    (T U : R) {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    1 + (0 : R) ^ (n * q) * T ^ ((n + 1) * q) * U = 1 := by
  have hprod : 0 < n * q := Nat.mul_pos hn hq
  have hne : n * q ≠ 0 := Nat.ne_of_gt hprod
  simp [hne]

/-- One anchored active step lowers the natural content depth. -/
theorem content_debt_drop (n : ℕ) : n < n + 1 :=
  Nat.lt_succ_self n

end PCRLean.Chambers.FrobeniusContent
