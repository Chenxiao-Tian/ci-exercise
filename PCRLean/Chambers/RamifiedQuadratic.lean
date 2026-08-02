import Mathlib

/-!
# Ramified quadratic collision: exact recurrence

The identities below are the algebraic core of the two standard charts of the
collision-cylinder blowup for `z^2 - u t^N`.  The accompanying arithmetic
lemmas formalize one-layer payment of the normalization/collision debt
`floor(N/2)`.
-/

namespace PCRLean.Chambers.RamifiedQuadratic

variable {R : Type*} [CommRing R]

/-- In the `t`-pivot chart, substitution `z = tz₁` factors the exceptional
square and lowers the ramification exponent by two. -/
theorem collision_factorization (t z u : R) (n : ℕ) :
    (t * z) ^ 2 - u * t ^ (n + 2) =
      t ^ 2 * (z ^ 2 - u * t ^ n) := by
  rw [mul_pow, pow_add]
  ring

/-- In the sibling `z`-pivot chart, substitution `t=zT` gives a controlled
transform whose exceptional restriction is a unit. -/
theorem sibling_factorization (z T u : R) (n : ℕ) :
    z ^ 2 - u * (z * T) ^ (n + 2) =
      z ^ 2 * (1 - u * z ^ n * T ^ (n + 2)) := by
  rw [mul_pow, pow_add]
  ring

@[simp] theorem sibling_exceptional_value (T u : R) (n : ℕ) :
    1 - u * (0 : R) ^ n * T ^ (n + 2) = if n = 0 then 1 - u * T ^ 2 else 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- For a genuine collision step (`n>0`), the sibling chart is terminal on the
exceptional divisor. -/
@[simp] theorem sibling_exceptional_value_of_pos (T u : R) {n : ℕ} (hn : 0 < n) :
    1 - u * (0 : R) ^ n * T ^ (n + 2) = 1 := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  simp [hne]

/-- The collision-debt length increases by exactly one when the exponent is
increased by two. -/
theorem debt_add_two (n : ℕ) : (n + 2) / 2 = n / 2 + 1 := by
  omega

@[simp] theorem even_debt (d : ℕ) : (2 * d) / 2 = d := by
  omega

@[simp] theorem odd_debt (d : ℕ) : (2 * d + 1) / 2 = d := by
  omega

/-- A collision step from exponent `n+2` to `n` strictly lowers the debt. -/
theorem debt_strict_drop (n : ℕ) : n / 2 < (n + 2) / 2 := by
  omega

end PCRLean.Chambers.RamifiedQuadratic
