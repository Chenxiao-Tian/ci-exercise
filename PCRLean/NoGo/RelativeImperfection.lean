import Mathlib
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative

/-!
# A smooth coordinate ring over a perfect field need not be perfect

Even when the coefficient field is perfect, the polynomial coordinate `X` has
no `p^e`-th root in `K[X]` for positive `e`.  This is the precise relative
obstruction left after the perfect-coefficient quasilinear cleaning theorem:
coefficients pulled back from the ground field can be rooted, but arbitrary
functions on a positive-dimensional smooth base cannot.
-/

namespace PCRLean.NoGo.RelativeImperfection

open Polynomial

variable {K : Type*} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- A positive Frobenius exponent has zero scalar derivative coefficient in
characteristic `p`. -/
theorem cast_prime_power_eq_zero {e : ℕ} (he : 0 < e) :
    (p ^ e : K) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  simp [pow_succ]

/-- Every positive `p^e`-th polynomial power has zero formal derivative. -/
theorem derivative_frobenius_power_zero (g : K[X]) {e : ℕ} (he : 0 < e) :
    derivative (g ^ (p ^ e)) = 0 := by
  rw [derivative_pow, cast_prime_power_eq_zero (K := K) p he]
  simp

/-- The affine coordinate `X` is not a positive Frobenius power in `K[X]`. -/
theorem X_not_frobenius_power {e : ℕ} (he : 0 < e) :
    ¬ ∃ g : K[X], g ^ (p ^ e) = X := by
  rintro ⟨g, hg⟩
  have hder := congrArg derivative hg
  rw [derivative_frobenius_power_zero (p := p) g he, derivative_X] at hder
  exact zero_ne_one hder

/-- In particular, the polynomial ring over a characteristic-`p` field is not
perfect in the Frobenius-surjective sense. -/
theorem frobenius_not_surjective :
    ¬ Function.Surjective (frobenius K[X] p) := by
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj X
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : g ^ p = X := by
    simpa [frobenius] using hg
  exact X_not_frobenius_power (K := K) p (e := 1) (by simp) ⟨g, by simpa using hpow⟩

end PCRLean.NoGo.RelativeImperfection
