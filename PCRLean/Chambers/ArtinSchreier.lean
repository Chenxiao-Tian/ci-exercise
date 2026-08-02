import Mathlib

/-!
# Artin-Schreier quadratic collision: exact two-parameter recurrence

This file formalizes the ring identity underlying the collision step
`(m+1,r+2) -> (m,r)` for `z^2 + t^m z + u t^r`, together with the exact
arithmetic of the frozen collision depth `min(m, floor(r/2))`.
-/

namespace PCRLean.Chambers.ArtinSchreier

variable {R : Type*} [CommRing R]

/-- Substitution `z = tz₁` factors the exceptional square and changes
`(m+1,r+2)` to `(m,r)`. -/
theorem collision_factorization (t z u : R) (m r : ℕ) :
    (t * z) ^ 2 + t ^ (m + 1) * (t * z) + u * t ^ (r + 2) =
      t ^ 2 * (z ^ 2 + t ^ m * z + u * t ^ r) := by
  rw [mul_pow, pow_succ, pow_add]
  ring

/-- The number of forced collision steps before a regular tail. -/
def collisionDepth (m r : ℕ) : ℕ := min m (r / 2)

/-- In the etale-tail regime `2m <= r`, the depth is exactly `m`. -/
theorem depth_of_etale_regime {m r : ℕ} (h : 2 * m ≤ r) :
    collisionDepth m r = m := by
  unfold collisionDepth
  rw [Nat.min_eq_left]
  omega

/-- In the odd wild-tail regime `r=2d+1<2m`, the depth is `d`. -/
theorem depth_of_odd_wild_regime {m d : ℕ} (h : d < m) :
    collisionDepth m (2 * d + 1) = d := by
  unfold collisionDepth
  have hdiv : (2 * d + 1) / 2 = d := by omega
  rw [hdiv, Nat.min_eq_right (Nat.le_of_lt h)]

/-- In the even radicial-tail regime `r=2d<2m`, the forced collision depth
is again `d`; the remaining tail is a different geometric packet. -/
theorem depth_of_even_radicial_regime {m d : ℕ} (h : d < m) :
    collisionDepth m (2 * d) = d := by
  unfold collisionDepth
  have hdiv : (2 * d) / 2 = d := by omega
  rw [hdiv, Nat.min_eq_right (Nat.le_of_lt h)]

end PCRLean.Chambers.ArtinSchreier
