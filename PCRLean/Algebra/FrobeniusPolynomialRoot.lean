import Mathlib
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Perfect
import PCRLean.NoGo.RelativeImperfection

/-!
# Exact Frobenius-root extraction for univariate polynomials

Over a perfect field of characteristic `p`, a univariate polynomial has zero
formal derivative exactly when it is a `p`-th power.  The forward proof is
constructive at the algebraic level: `contract` removes the exponent factor
`p`, inverse Frobenius roots every coefficient, and `expand_contract` rebuilds
the original polynomial.

This theorem supplies an exact arbitrary-input packet extractor in one
polynomial direction.  It does not assert the analogous relative statement
for coefficients in a positive-dimensional smooth coordinate ring; the
`RelativeImperfection` module proves why that stronger statement is false.
-/

noncomputable section

namespace PCRLean.Algebra.FrobeniusPolynomialRoot

open Polynomial

variable {K : Type*} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The canonical polynomial obtained by contracting all `p`-divisible
exponents and taking inverse-Frobenius roots of the coefficients. -/
noncomputable def rootPolynomial (f : K[X]) : K[X] :=
  (contract p f).map (frobeniusEquiv K p).symm

/-- A derivative-zero polynomial is exactly reconstructed as the `p`-th power
of its canonical contracted coefficient root. -/
theorem rootPolynomial_pow_of_derivative_eq_zero {f : K[X]}
    (hf : derivative f = 0) :
    (rootPolynomial p f) ^ p = f := by
  calc
    (rootPolynomial p f) ^ p = expand K p (contract p f) := by
      symm
      simpa [rootPolynomial] using
        (polynomial_expand_eq (R := K) (p := p) (contract p f))
    _ = f := Polynomial.expand_contract p hf (Fact.out : p.Prime).ne_zero

/-- Any `p`-th polynomial power has zero derivative. -/
theorem derivative_eq_zero_of_eq_pow {f g : K[X]} (h : g ^ p = f) :
    derivative f = 0 := by
  rw [← h]
  simpa using
    (PCRLean.NoGo.RelativeImperfection.derivative_frobenius_power_zero
      (K := K) p g (e := 1) (by simp))

/-- Exact univariate Frobenius criterion over a perfect field. -/
theorem derivative_eq_zero_iff_exists_frobenius_root (f : K[X]) :
    derivative f = 0 ↔ ∃ g : K[X], g ^ p = f := by
  constructor
  · intro hf
    exact ⟨rootPolynomial p f, rootPolynomial_pow_of_derivative_eq_zero p hf⟩
  · rintro ⟨g, hg⟩
    exact derivative_eq_zero_of_eq_pow p hg

/-- The canonical root is unique because Frobenius is injective on the reduced
polynomial ring. -/
theorem frobenius_root_unique {f g h : K[X]}
    (hg : g ^ p = f) (hh : h ^ p = f) : g = h := by
  apply frobenius_inj K[X] p
  simpa [frobenius] using hg.trans hh.symm

end PCRLean.Algebra.FrobeniusPolynomialRoot
