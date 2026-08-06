import Mathlib
import PCRLean.PolynomialFrobeniusExtraction

/-!
# Relative quasilinear extraction over a smooth one-dimensional base

Let `B = K[t]`, with `K` perfect of characteristic `p`.  A diagonal
quasilinear form `Σ aᵢ(t) Yᵢᵖ` has a sharp dichotomy.  If every coefficient has
zero base derivative, every coefficient has a canonical `p`th root and the
whole form is one `p`th power.  Otherwise a coefficient has a nonzero base
derivative, providing the transverse base symbol used by the radicial escape
branch.

This is the exact relative-imperfection theorem missing from naive
coefficientwise root extraction.
-/

namespace PCRLean
namespace RelativeQuasilinearExtraction

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectRing K p]

abbrev Base := K[X]
abbrev Ambient := MvPolynomial σ (Base (K := K))

/-- A diagonal relative quasilinear form. -/
def form (a : σ → Base (K := K)) : Ambient (K := K) (σ := σ) :=
  ∑ i : σ, MvPolynomial.C (a i) * (MvPolynomial.X i) ^ p

/-- The canonical coefficientwise root obtained from zero-derivative
coefficients. -/
def rootCoefficient (a : σ → Base (K := K)) (i : σ) : Base (K := K) :=
  PolynomialFrobeniusExtraction.frobeniusRoot p (a i)

/-- The corresponding relative linear root. -/
def linearRoot (a : σ → Base (K := K)) : Ambient (K := K) (σ := σ) :=
  ∑ i : σ, MvPolynomial.C (rootCoefficient p a i) * MvPolynomial.X i

/-- Frobenius carries a finite sum to the sum of `p`th powers. -/
theorem finset_sum_pow
    (s : Finset σ) (f : σ → Ambient (K := K) (σ := σ)) :
    (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, (f i) ^ p := by
  have h := map_sum (frobenius (Ambient (K := K) (σ := σ)) p)
    (fun i : σ => f i) s
  simpa [frobenius_def] using h.symm

/-- If all base derivatives vanish, the quasilinear form is exactly the `p`th
power of its canonical relative linear root. -/
theorem form_eq_linearRoot_pow
    (a : σ → Base (K := K))
    (hderiv : ∀ i, Polynomial.derivative (a i) = 0) :
    form p a = (linearRoot p a) ^ p := by
  classical
  rw [form, linearRoot]
  rw [finset_sum_pow (p := p) Finset.univ
    (fun i => MvPolynomial.C (rootCoefficient p a i) * MvPolynomial.X i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, map_pow]
  rw [PolynomialFrobeniusExtraction.frobeniusRoot_pow_eq p (a i) (hderiv i)]
  rfl

/-- The relative Frobenius-extraction dichotomy. -/
theorem extraction_or_transverse
    (a : σ → Base (K := K)) :
    (∃ b : σ → Base (K := K),
      form p a = (∑ i : σ, MvPolynomial.C (b i) * MvPolynomial.X i) ^ p) ∨
    (∃ i, Polynomial.derivative (a i) ≠ 0) := by
  classical
  by_cases h : ∀ i, Polynomial.derivative (a i) = 0
  · left
    refine ⟨rootCoefficient p a, ?_⟩
    exact form_eq_linearRoot_pow p a h
  · right
    push_neg at h
    exact h

/-- In the extracted branch, every coefficient root is canonical. -/
theorem extracted_coefficient_pow
    (a : σ → Base (K := K))
    (hderiv : ∀ i, Polynomial.derivative (a i) = 0) (i : σ) :
    (rootCoefficient p a i) ^ p = a i :=
  PolynomialFrobeniusExtraction.frobeniusRoot_pow_eq p (a i) (hderiv i)

end

end RelativeQuasilinearExtraction
end PCRLean
