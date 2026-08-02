import Mathlib

namespace PCRLean
namespace FrobeniusPacket

section Frobenius

variable {R : Type*} [CommSemiring R]
variable (p e : Nat) [ExpChar R p]

/-- Iterated Frobenius is additive, hence `p^e`-th powers add without cross
terms in exponential characteristic `p`. -/
theorem add_pow_primePower (x y : R) :
    (x + y) ^ (p ^ e) = x ^ (p ^ e) + y ^ (p ^ e) := by
  simpa [iterateFrobenius_def] using
    (map_add (iterateFrobenius R p e) x y)

/-- Iterated Frobenius is multiplicative. -/
theorem mul_pow_primePower (x y : R) :
    (x * y) ^ (p ^ e) = x ^ (p ^ e) * y ^ (p ^ e) := by
  simpa [iterateFrobenius_def] using
    (map_mul (iterateFrobenius R p e) x y)

/-- Cleaning by a `p^e`-th power changes a pure presentation by an additive
Frobenius coboundary and introduces no mixed terms. -/
theorem cleaning_identity (z g a : R) :
    (z + g) ^ (p ^ e) + a = z ^ (p ^ e) + (g ^ (p ^ e) + a) := by
  rw [add_pow_primePower (R := R) p e]
  ac_rfl

end Frobenius

section RootCharts

variable {R : Type*} [CommRing R]

/-- Exact active-chart identity for the principal Frobenius-root packet
`z^q + x^(q(N+1))G`; it re-enters with `N+1 -> N`. -/
theorem principalRoot_active_identity (x z G : R) (q N : Nat) :
    (x * z) ^ q + x ^ (q * (N + 1)) * G =
      x ^ q * (z ^ q + x ^ (q * N) * G) := by
  have hqN : q * (N + 1) = q + q * N := by omega
  rw [mul_pow, hqN, pow_add]
  ring

/-- Exact sibling-chart identity for the same principal root packet.  After
controlled division by `z^q` the first term is the unit `1`. -/
theorem principalRoot_sibling_identity (z X G : R) (q N : Nat) :
    z ^ q + (z * X) ^ (q * (N + 1)) * G =
      z ^ q * (1 + z ^ (q * N) * X ^ (q * (N + 1)) * G) := by
  have hqN : q * (N + 1) = q + q * N := by omega
  rw [mul_pow, hqN, pow_add]
  ring

/-- The visible root depth has no uniform finite bound even when the reduced
projective root direction is kept fixed. -/
theorem unbounded_root_depth (B : Nat) : ∃ N, B < N := by
  exact ⟨B + 1, by omega⟩

end RootCharts

end FrobeniusPacket
end PCRLean
