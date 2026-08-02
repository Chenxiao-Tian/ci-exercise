import Mathlib

/-!
# Odd-contact radicial cusp: exact chart identities

This file formalizes the algebraic core of the repeated point blowups for
`y^2 + s^(2N+1)`.  It deliberately proves only exact identities and the
well-founded numerical debt drop.  Scheme-level regularity, permissibility,
strict transforms, and SNC assertions are separate interfaces.
-/

namespace PCRLean.Chambers.OddCusp

/-- The odd contact exponent `2n+1`. -/
def oddExp (n : ℕ) : ℕ := 2 * n + 1

@[simp] theorem oddExp_zero : oddExp 0 = 1 := by
  simp [oddExp]

theorem oddExp_succ (n : ℕ) : oddExp (n + 1) = oddExp n + 2 := by
  simp only [oddExp]
  omega

theorem oddExp_pos (n : ℕ) : 0 < oddExp n := by
  simp only [oddExp]
  omega

variable {R : Type*} [CommRing R]

/--
In the `s`-pivot chart, substituting `y = sY` into the cusp of debt `n+1`
and dividing by the exceptional square gives the cusp of debt `n`.
-/
theorem sChart_factorization (s Y : R) (n : ℕ) :
    (s * Y) ^ 2 + s ^ oddExp (n + 1) =
      s ^ 2 * (Y ^ 2 + s ^ oddExp n) := by
  rw [oddExp_succ, pow_add]
  ring

/--
In the sibling `y`-pivot chart, substituting `s = yS` exposes a controlled
transform whose restriction to the exceptional divisor is the unit `1`.
-/
theorem yChart_factorization (y S : R) (n : ℕ) :
    y ^ 2 + (y * S) ^ oddExp (n + 1) =
      y ^ 2 * (1 + y ^ oddExp n * S ^ oddExp (n + 1)) := by
  rw [mul_pow, oddExp_succ, pow_add]
  ring

@[simp] theorem yChart_exceptional_value (S : R) (n : ℕ) :
    1 + (0 : R) ^ oddExp n * S ^ oddExp (n + 1) = 1 := by
  simp [oddExp]

/-- Every active cusp step lowers the integer debt by one. -/
theorem debt_drop (n : ℕ) : n < n + 1 :=
  Nat.lt_succ_self n

end PCRLean.Chambers.OddCusp
