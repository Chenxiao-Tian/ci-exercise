import Mathlib
import PCRLean.Experimental.PerfectFrobeniusSupportRoot
import PCRLean.Experimental.FrobeniusRootDegreeDescent

/-!
# Derivative-zero Frobenius descent over a perfect field

For a multivariate polynomial over a field of characteristic `p`, vanishing of
all first partial derivatives forces every exponent in every supported monomial
to be divisible by `p`.  Over a perfect field the coefficient obstruction also
vanishes, so the polynomial has an explicit `p`-th root.  If the polynomial is
nonconstant, passing to this root strictly lowers total degree.

This separates the two genuine obstructions in the rank-zero chamber:

* exponent divisibility is forced by derivative vanishing;
* coefficient root extraction requires perfectness (or a radicial extension).

The theorem is valid for an arbitrary variable type; every polynomial has
finite support, so no global finiteness hypothesis on the variables is needed.
The main dichotomy says that a nonconstant polynomial either has a visible
first derivative or admits a strict Frobenius-root descent.
-/

namespace PCRLean
namespace Experimental
namespace PDerivFrobeniusDescent

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- The Euler operator `X_i ∂_i` acts diagonally on coefficients. -/
theorem coeff_X_mul_pderiv
    (f : MvPolynomial σ K) (i : σ) (m : σ →₀ Nat) :
    MvPolynomial.coeff m
        (MvPolynomial.X i * MvPolynomial.pderiv i f) =
      (m i : K) * MvPolynomial.coeff m f := by
  induction f using MvPolynomial.induction_on' with
  | monomial n a =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      by_cases hnm : n = m
      · subst n
        simp [nsmul_eq_mul]
      · simp [MvPolynomial.coeff_monomial, hnm]
  | add f g hf hg =>
      simp [map_add, mul_add, hf, hg, mul_add]

/-- If one partial derivative vanishes, every supported exponent in that
coordinate is divisible by the characteristic. -/
theorem exponent_dvd_of_pderiv_eq_zero
    (f : MvPolynomial σ K) (i : σ)
    (hderiv : MvPolynomial.pderiv i f = 0)
    {m : σ →₀ Nat} (hm : m ∈ f.support) :
    p ∣ m i := by
  have hcoeff : MvPolynomial.coeff m f ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hzero : (m i : K) * MvPolynomial.coeff m f = 0 := by
    rw [← coeff_X_mul_pderiv f i m, hderiv]
    simp
  have hcast : (m i : K) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hcoeff
  exact (CharP.cast_eq_zero_iff K p (m i)).mp hcast

/-- Vanishing of every first partial derivative forces support divisibility by
`p` in every coordinate. -/
theorem exponentDivisible_one_of_all_pderiv_zero
    (f : MvPolynomial σ K)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0) :
    PerfectFrobeniusSupportRoot.ExponentDivisible p 1 f := by
  intro m hm i
  simpa using exponent_dvd_of_pderiv_eq_zero p f i (hderiv i) hm

section Perfect

variable [PerfectField K p]

/-- Explicit perfect-field root recovered from derivative vanishing. -/
def derivativeRoot (f : MvPolynomial σ K) : MvPolynomial σ K :=
  PerfectFrobeniusSupportRoot.rootPolynomial p 1 f

/-- The explicit derivative root has `p`-th power equal to the original
polynomial. -/
theorem derivativeRoot_pow
    (f : MvPolynomial σ K)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0) :
    (derivativeRoot p f) ^ p = f := by
  simpa [derivativeRoot] using
    PerfectFrobeniusSupportRoot.rootPolynomial_pow p 1 f
      (exponentDivisible_one_of_all_pderiv_zero p f hderiv)

/-- A nonzero polynomial has a nonzero derivative root. -/
theorem derivativeRoot_ne_zero
    (f : MvPolynomial σ K)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0)
    (hf : f ≠ 0) : derivativeRoot p f ≠ 0 := by
  exact PerfectFrobeniusSupportRoot.rootPolynomial_ne_zero p 1 f
    (exponentDivisible_one_of_all_pderiv_zero p f hderiv) hf

/-- A nonconstant derivative-zero polynomial has a nonconstant root. -/
theorem derivativeRoot_totalDegree_pos
    (f : MvPolynomial σ K)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0)
    (hf : 0 < f.totalDegree) :
    0 < (derivativeRoot p f).totalDegree := by
  have hpow := derivativeRoot_pow p f hderiv
  rw [← hpow, MvPolynomial.totalDegree_pow] at hf
  have hp : 0 < p := (Fact.out : p.Prime).pos
  omega

/-- Passing to the derivative root strictly lowers total degree for every
nonconstant derivative-zero polynomial. -/
theorem derivativeRoot_totalDegree_lt
    (f : MvPolynomial σ K)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0)
    (hf : 0 < f.totalDegree) :
    (derivativeRoot p f).totalDegree < f.totalDegree := by
  rw [← derivativeRoot_pow p f hderiv]
  exact FrobeniusRootDegreeDescent.iteratedRoot_totalDegree_lt p 1
    (by omega) _ (derivativeRoot_totalDegree_pos p f hderiv hf)

/-- First-order visibility of a polynomial. -/
def DerivativeVisible (f : MvPolynomial σ K) : Prop :=
  ∃ i, MvPolynomial.pderiv i f ≠ 0

/-- Every nonconstant polynomial is either visible to a first partial
derivative or admits a strict perfect-field Frobenius-root descent. -/
theorem visible_or_strict_root
    (f : MvPolynomial σ K) (hf : 0 < f.totalDegree) :
    DerivativeVisible f ∨
      ∃ g : MvPolynomial σ K,
        f = g ^ p ∧ 0 < g.totalDegree ∧ g.totalDegree < f.totalDegree := by
  by_cases hvis : DerivativeVisible f
  · exact Or.inl hvis
  · have hzero : ∀ i, MvPolynomial.pderiv i f = 0 := by
      intro i
      by_contra hi
      exact hvis ⟨i, hi⟩
    refine Or.inr ⟨derivativeRoot p f, ?_, ?_, ?_⟩
    · exact (derivativeRoot_pow p f hzero).symm
    · exact derivativeRoot_totalDegree_pos p f hzero hf
    · exact derivativeRoot_totalDegree_lt p f hzero hf

end Perfect

end

end PDerivFrobeniusDescent
end Experimental
end PCRLean
