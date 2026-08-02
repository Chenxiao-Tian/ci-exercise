import Mathlib

/-!
# Ramified quadratic collision: exact recurrence

The identity below is the algebraic core of the collision-cylinder blowup
`N+2 -> N` for `z^2 - u t^N`.  The accompanying arithmetic lemmas formalize
one-layer payment of the normalization/collision debt `floor(N/2)`.
-/

namespace PCRLean.Chambers.RamifiedQuadratic

variable {R : Type*} [CommRing R]

/-- Substitution `z = tz₁` factors the exceptional square and lowers the
ramification exponent by two. -/
theorem collision_factorization (t z u : R) (n : ℕ) :
    (t * z) ^ 2 - u * t ^ (n + 2) =
      t ^ 2 * (z ^ 2 - u * t ^ n) := by
  rw [mul_pow, pow_add]
  ring

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
