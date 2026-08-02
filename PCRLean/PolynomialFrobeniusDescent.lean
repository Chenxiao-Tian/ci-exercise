import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Perfect

/-!
# One-variable Frobenius descent for differential principal ideals

Over a perfect field of characteristic `p`, a polynomial with zero derivative
is a `p`-th power. Consequently, if the principal ideal `(f)` is stable under
the ordinary derivation, then `f` has an actual polynomial Frobenius root.

This is the one-dimensional affine model of Cartier descent for differential
ideals. The higher-dimensional resolution program needs its finite-level
Hasse-operator and locally free relative-Frobenius analogue.
-/

namespace PCRLean
namespace PolynomialFrobeniusDescent

noncomputable section

open Polynomial

universe u

variable {K : Type u} (p : ℕ)
variable [Field K] [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The canonical polynomial root obtained by contracting exponents and taking
canonical coefficient roots. -/
def frobeniusRoot (f : K[X]) : K[X] :=
  (Polynomial.contract p f).map (frobeniusEquiv K p).symm

/-- A polynomial with zero derivative is exactly the `p`-th power of its
canonical Frobenius root. -/
theorem frobeniusRoot_pow_of_derivative_eq_zero
    {f : K[X]} (hf : Polynomial.derivative f = 0) :
    (frobeniusRoot (K := K) p f) ^ p = f := by
  calc
    (frobeniusRoot (K := K) p f) ^ p =
        Polynomial.expand K p (Polynomial.contract p f) := by
      exact (polynomial_expand_eq
        (R := K) (p := p) (Polynomial.contract p f)).symm
    _ = f := Polynomial.expand_contract p hf
      (Fact.out : p.Prime).ne_zero

/-- Zero derivative is equivalent to existence of a polynomial `p`-th root
when the coefficient field is perfect. -/
theorem derivative_eq_zero_iff_exists_pow
    (f : K[X]) :
    Polynomial.derivative f = 0 ↔ ∃ g : K[X], g ^ p = f := by
  constructor
  · intro hf
    exact ⟨frobeniusRoot (K := K) p f,
      frobeniusRoot_pow_of_derivative_eq_zero (K := K) p hf⟩
  · rintro ⟨g, rfl⟩
    rw [Polynomial.derivative_pow]
    have hpzero : (p : K) = 0 := CharP.cast_eq_zero K p
    rw [hpzero, map_zero, zero_mul]

/-- Stability of the principal ideal under ordinary differentiation forces an
actual Frobenius root. -/
theorem exists_pow_of_derivative_mem_principal
    (f : K[X])
    (hstable : Polynomial.derivative f ∈ Ideal.span ({f} : Set K[X])) :
    ∃ g : K[X], g ^ p = f := by
  rw [Ideal.mem_span_singleton] at hstable
  have hzero : Polynomial.derivative f = 0 :=
    (Polynomial.dvd_derivative_iff).mp hstable
  exact (derivative_eq_zero_iff_exists_pow (K := K) p f).mp hzero

/-- The canonical Frobenius root is unique. -/
theorem frobeniusRoot_unique
    (f g : K[X]) (hg : g ^ p = f) :
    g = frobeniusRoot (K := K) p f := by
  apply frobenius_inj K[X] p
  simpa [frobenius_def, hg,
    frobeniusRoot_pow_of_derivative_eq_zero (K := K) p
      ((derivative_eq_zero_iff_exists_pow (K := K) p f).2 ⟨g, hg⟩)]

end

end PolynomialFrobeniusDescent
end PCRLean
