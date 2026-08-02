import Mathlib
import PCRLean.Chambers.ArtinSchreier

/-!
# Purely inseparable quadratic tails in characteristic two

This module formalizes the exact algebraic identities left by the even
Artin--Schreier tail.  It records square-gauge invariance, the forced
collision recurrence, the two final affine charts, and the pure no-linear-term
specialization.  Regularity of the radicial branch and the existence of a
scheme-level permissible centre remain separate geometric interfaces.
-/

namespace PCRLean.Chambers.PurelyInseparable

variable {R : Type*} [CommRing R]

/-- In characteristic two, translating a quadratic root changes the constant
term by a square and leaves the equation unchanged. -/
theorem square_gauge [CharP R 2] (Y h u : R) :
    (Y + h) ^ 2 + (u + h ^ 2) = Y ^ 2 + u := by
  rw [CharTwo.add_sq]
  calc
    Y ^ 2 + h ^ 2 + (u + h ^ 2) = Y ^ 2 + u + (h ^ 2 + h ^ 2) := by
      ac_rfl
    _ = Y ^ 2 + u := by
      rw [CharTwo.add_self_eq_zero, add_zero]

/-- One forced collision-cylinder blowup changes the even tail
`(n+1, 2d+2)` to `(n, 2d)`. -/
theorem even_collision_factorization (t z u : R) (n d : ℕ) :
    (t * z) ^ 2 + t ^ (n + 1) * (t * z) + u * t ^ (2 * d + 2) =
      t ^ 2 * (z ^ 2 + t ^ n * z + u * t ^ (2 * d)) := by
  simpa using
    (PCRLean.Chambers.ArtinSchreier.collision_factorization
      (R := R) t z u n (2 * d))

/-- The final `t`-pivot chart of the even tail. -/
theorem final_t_pivot (t y u : R) (n : ℕ) :
    (t * y) ^ 2 + t ^ (n + 1) * (t * y) + u * t ^ 2 =
      t ^ 2 * (y ^ 2 + t ^ n * y + u) := by
  simpa using
    (PCRLean.Chambers.ArtinSchreier.collision_factorization
      (R := R) t y u n 0)

/-- The final sibling `z`-pivot chart of the even tail. -/
theorem final_z_pivot (z T u : R) (n : ℕ) :
    z ^ 2 + (z * T) ^ (n + 1) * z + u * (z * T) ^ 2 =
      z ^ 2 * (1 + z ^ n * T ^ (n + 1) + u * T ^ 2) := by
  simpa using
    (PCRLean.Chambers.ArtinSchreier.sibling_factorization
      (R := R) z T u n 0)

/-- In the genuinely purely inseparable no-linear-term family, one collision
blowup lowers the even exponent by two. -/
theorem pure_collision_factorization (t z u : R) (d : ℕ) :
    (t * z) ^ 2 + u * t ^ (2 * d + 2) =
      t ^ 2 * (z ^ 2 + u * t ^ (2 * d)) := by
  rw [mul_pow]
  have hexp : 2 * d + 2 = 2 + 2 * d := by omega
  rw [hexp, pow_add]
  ring

/-- The forced even collision depth drops by one. -/
theorem even_depth_drop (d : ℕ) : d < d + 1 :=
  Nat.lt_succ_self d

/-- At depth zero the collision phase has reached the radicial tail rather
than an etale or wild branch. -/
inductive ExitKind where
  | radicialTransverse
  | radicialCritical
  deriving DecidableEq, Repr

end PCRLean.Chambers.PurelyInseparable
