import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Expand
import PCRLean.Experimental.PolynomialHasseFrobenius

/-!
# Imperfect-field coefficient obstruction

Derivative vanishing controls exponents, not coefficients.  Over a field of
characteristic `p`, the polynomial `a X^p` has zero derivative for every `a`.
If `a` is not a `p`-th power in the coefficient field, however, the polynomial
has no polynomial `p`-th root.

This is the minimal obstruction to removing perfectness from the rank-zero
Frobenius descent.  Any imperfect-field resolution proof must pass to a finite
radicial coefficient extension and descend the resulting centre or replace
coefficient roots by a different intrinsic object.
-/

namespace PCRLean
namespace Experimental
namespace ImperfectCoefficientObstruction

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- The basic coefficient-obstruction polynomial. -/
def obstructionPolynomial (a : K) : Polynomial K :=
  Polynomial.monomial p a

/-- Its ordinary derivative vanishes in characteristic `p`. -/
theorem derivative_obstructionPolynomial (a : K) :
    Polynomial.derivative (obstructionPolynomial p a) = 0 := by
  rw [obstructionPolynomial, Polynomial.derivative_monomial]
  have hp : (p : K) = 0 := CharP.cast_eq_zero K p
  simp [hp]

/-- Any polynomial `p`-th root of `a X^p` forces `a` itself to be a `p`-th
power. -/
theorem coefficient_is_pow_of_polynomial_root
    (a : K) (g : Polynomial K)
    (hroot : g ^ p = obstructionPolynomial p a) :
    ∃ b : K, b ^ p = a := by
  refine ⟨g.coeff 1, ?_⟩
  have hcoeff := congrArg (fun h : Polynomial K => h.coeff p) hroot
  have hpow :=
    PolynomialHasseFrobenius.coeff_pow_prime_mul p g 1
  rw [one_mul] at hpow
  rw [hpow] at hcoeff
  simpa [obstructionPolynomial] using hcoeff

/-- A coefficient outside the Frobenius image gives a derivative-zero
polynomial with no polynomial `p`-th root. -/
theorem no_polynomial_root_of_not_coefficient_pow
    (a : K) (ha : ¬ ∃ b : K, b ^ p = a) :
    ¬ ∃ g : Polynomial K, g ^ p = obstructionPolynomial p a := by
  rintro ⟨g, hg⟩
  exact ha (coefficient_is_pow_of_polynomial_root p a g hg)

/-- Complete minimal imperfect-field boundary certificate. -/
theorem derivative_zero_but_no_root
    (a : K) (ha : ¬ ∃ b : K, b ^ p = a) :
    Polynomial.derivative (obstructionPolynomial p a) = 0 ∧
      ¬ ∃ g : Polynomial K, g ^ p = obstructionPolynomial p a :=
  ⟨derivative_obstructionPolynomial p a,
    no_polynomial_root_of_not_coefficient_pow p a ha⟩

end

end ImperfectCoefficientObstruction
end Experimental
end PCRLean
