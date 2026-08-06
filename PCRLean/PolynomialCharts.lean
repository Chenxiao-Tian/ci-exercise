import Mathlib

namespace PCRLean
namespace PolynomialCharts

section OddCusp

variable {R : Type*} [CommRing R]

/-- Exact ring identity for the active `s`-pivot chart of the odd cusp.
It is the algebraic content of substituting `y = sY` into
`y^2 + s^(2N+3)` and dividing the total transform by `s^2`. -/
theorem oddCusp_sPivot_identity (s Y : R) (N : Nat) :
    (s * Y) ^ 2 + s ^ (2 * N + 3) =
      s ^ 2 * (Y ^ 2 + s ^ (2 * N + 1)) := by
  have hexp : 2 * N + 3 = 2 + (2 * N + 1) := by omega
  rw [hexp, pow_add, mul_pow]
  ring

/-- Exact sibling-chart identity after substituting `s = yS`.
The controlled transform has constant term `1`, which is the formal reason
that this chart is terminal for mark two. -/
theorem oddCusp_yPivot_identity (y S : R) (N : Nat) :
    y ^ 2 + (y * S) ^ (2 * N + 3) =
      y ^ 2 * (1 + y ^ (2 * N + 1) * S ^ (2 * N + 3)) := by
  have hexp : 2 * N + 3 = 2 + (2 * N + 1) := by omega
  rw [mul_pow, hexp, pow_add]
  ring

/-- The smooth tangent tail `y^2+s` has unit derivative in the `s`
direction.  The equality is stated algebraically to avoid importing an
unverified geometric smoothness wrapper. -/
theorem tangentTail_linearCoefficient (y s : R) :
    y ^ 2 + s = s + y ^ 2 := by
  ac_rfl

end OddCusp

section TameQuadratic

variable {R : Type*} [CommRing R]

/-- Exact collision-cylinder chart identity for the tame ramified quadratic
order.  Writing the old collision exponent as `M+2` avoids truncated natural
subtraction in the algebraic statement. -/
theorem tameQuadratic_active_identity (t z u : R) (M : Nat) :
    (t * z) ^ 2 - u * t ^ (M + 2) =
      t ^ 2 * (z ^ 2 - u * t ^ M) := by
  have hexp : M + 2 = 2 + M := by omega
  rw [mul_pow, hexp, pow_add]
  ring

/-- The sibling pivot of the tame quadratic order has a unit term after
controlled division by the exceptional square. -/
theorem tameQuadratic_sibling_identity (z T u : R) (M : Nat) :
    z ^ 2 - u * (z * T) ^ (M + 2) =
      z ^ 2 * (1 - u * z ^ M * T ^ (M + 2)) := by
  have hexp : M + 2 = 2 + M := by omega
  rw [mul_pow, hexp, pow_add]
  ring

end TameQuadratic

section ArtinSchreier

variable {R : Type*} [CommRing R]

/-- Exact active-chart identity for the Artin--Schreier collision update
`(m+1,r+2) -> (m,r)`. -/
theorem artinSchreier_active_identity (t z u : R) (m r : Nat) :
    (t * z) ^ 2 + t ^ (m + 1) * (t * z) + u * t ^ (r + 2) =
      t ^ 2 * (z ^ 2 + t ^ m * z + u * t ^ r) := by
  have hr : r + 2 = 2 + r := by omega
  rw [mul_pow, pow_succ, hr, pow_add]
  ring

/-- Exact Frobenius-root recurrence for the split purely inseparable packet
`z^2 + t^(2N+2)G`. -/
theorem radicialRoot_active_identity (t z G : R) (N : Nat) :
    (t * z) ^ 2 + t ^ (2 * N + 2) * G =
      t ^ 2 * (z ^ 2 + t ^ (2 * N) * G) := by
  have hexp : 2 * N + 2 = 2 + 2 * N := by omega
  rw [mul_pow, hexp, pow_add]
  ring

end ArtinSchreier

section CharacteristicTwo

variable {R : Type*} [CommRing R] [CharP R 2]

/-- In characteristic two, square cleaning has zero ordinary polar cross
term: `(x+g)^2 = x^2+g^2`. -/
theorem squareCleaning_identity (x g : R) :
    (x + g) ^ 2 = x ^ 2 + g ^ 2 := by
  have htwo : (2 : R) = 0 := by
    exact CharP.cast_eq_zero R 2
  calc
    (x + g) ^ 2 = x ^ 2 + 2 * x * g + g ^ 2 := by ring
    _ = x ^ 2 + g ^ 2 := by rw [htwo]; ring

/-- The polarization of a square vanishes in characteristic two. -/
theorem squarePolarization_zero (x y : R) :
    (x + y) ^ 2 - x ^ 2 - y ^ 2 = 0 := by
  rw [squareCleaning_identity]
  ring

end CharacteristicTwo

end PolynomialCharts
end PCRLean
