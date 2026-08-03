import Mathlib
import PCRLean.Experimental.PerfectFrobeniusRankZeroEscape
import PCRLean.Experimental.InitialFormFrobeniusCleaning

/-!
# Frobenius support heredity over coefficient domains

The exact support-scaling theorem for a prime-power Frobenius power does not
require field coefficients.  It only needs prime characteristic and absence of
zero divisors, so that a nonzero coefficient remains nonzero after a positive
power.

For a commutative domain-like coefficient ring `A`, raising a multivariate
polynomial to `p^e` scales every supported exponent by `p^e` and raises every
coefficient to the same power.  Consequently the support lower-bound order
satisfies

`OrderGE (g^(p^e)) ((p^e)*m) ↔ OrderGE g m`.

The generalization is important because, after splitting passive and normal
variables, the coefficient ring for the normal polynomial is itself a
polynomial ring rather than a field.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusSupportDomain

noncomputable section

universe u v

variable {A : Type u} [CommRing A] [NoZeroDivisors A] [Nontrivial A]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP A p]

open InitialFormFrobeniusCleaning

/-- Scale every exponent by a natural number. -/
def scaleExponent (q : Nat) (d : σ →₀ Nat) : σ →₀ Nat :=
  q • d

/-- Positive exponent scaling is injective. -/
theorem scaleExponent_injective
    (q : Nat) (hq : 0 < q) :
    Function.Injective (scaleExponent (σ := σ) q) := by
  intro d₁ d₂ h
  ext i
  have hi := congrArg (fun d : σ →₀ Nat => d i) h
  simpa [scaleExponent] using Nat.eq_of_mul_eq_mul_left hq hi

/-- Total monomial degree scales with the exponent vector. -/
theorem exponentDegree_scale
    (q : Nat) (d : σ →₀ Nat) :
    exponentDegree (scaleExponent q d) = q * exponentDegree d := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [scaleExponent, exponentDegree]
  | @single_add i a d hi ha ih =>
      simp [scaleExponent, exponentDegree, hi, ha, ih, mul_add]

/-- Exact finite monomial expansion of a prime-power Frobenius power. -/
theorem frobeniusPower_expansion
    (e : Nat) (g : MvPolynomial σ A) :
    g ^ (p ^ e) =
      ∑ d in g.support,
        MvPolynomial.monomial (scaleExponent (p ^ e) d)
          ((MvPolynomial.coeff d g) ^ (p ^ e)) := by
  classical
  calc
    g ^ (p ^ e) =
        (∑ d in g.support,
          MvPolynomial.monomial d (MvPolynomial.coeff d g)) ^ (p ^ e) := by
      rw [MvPolynomial.sum_monomial_coeff]
    _ = ∑ d in g.support,
          (MvPolynomial.monomial d (MvPolynomial.coeff d g)) ^ (p ^ e) :=
      PerfectFrobeniusRankZeroEscape.finset_sum_pow_char_pow
        p g.support
        (fun d => MvPolynomial.monomial d (MvPolynomial.coeff d g)) e
    _ = ∑ d in g.support,
        MvPolynomial.monomial (scaleExponent (p ^ e) d)
          ((MvPolynomial.coeff d g) ^ (p ^ e)) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [MvPolynomial.monomial_pow, scaleExponent]

/-- Every supported root monomial survives at the scaled exponent. -/
theorem scaled_mem_support
    (e : Nat) (g : MvPolynomial σ A)
    {d : σ →₀ Nat} (hd : d ∈ g.support) :
    scaleExponent (p ^ e) d ∈ (g ^ (p ^ e)).support := by
  classical
  have hcoeff : (MvPolynomial.coeff d g) ^ (p ^ e) ≠ 0 :=
    pow_ne_zero _ (MvPolynomial.mem_support_iff.mp hd)
  rw [MvPolynomial.mem_support_iff, frobeniusPower_expansion]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simpa [hcoeff]
  · intro b hb hbd
    rw [if_neg]
    intro hscale
    apply hbd
    exact scaleExponent_injective (σ := σ) (p ^ e)
      (pow_pos (Fact.out : p.Prime).pos e) hscale
  · intro hdnot
    exact (hdnot hd).elim

/-- Every supported monomial of the power comes from a supported root
monomial. -/
theorem mem_support_power_exists_scaled
    (e : Nat) (g : MvPolynomial σ A)
    {m : σ →₀ Nat} (hm : m ∈ (g ^ (p ^ e)).support) :
    ∃ d ∈ g.support, scaleExponent (p ^ e) d = m := by
  rw [frobeniusPower_expansion] at hm
  have hsub := MvPolynomial.support_sum
    (s := g.support)
    (f := fun d => MvPolynomial.monomial (scaleExponent (p ^ e) d)
      ((MvPolynomial.coeff d g) ^ (p ^ e)))
  have hmem := hsub hm
  simp only [Finset.mem_biUnion] at hmem
  rcases hmem with ⟨d, hd, hmmono⟩
  have hsingleton := MvPolynomial.support_monomial_subset hmmono
  have heq : m = scaleExponent (p ^ e) d := by
    simpa using hsingleton
  exact ⟨d, hd, heq.symm⟩

/-- Exact support characterization. -/
theorem mem_support_power_iff
    (e : Nat) (g : MvPolynomial σ A) (m : σ →₀ Nat) :
    m ∈ (g ^ (p ^ e)).support ↔
      ∃ d ∈ g.support, scaleExponent (p ^ e) d = m := by
  constructor
  · exact mem_support_power_exists_scaled p e g
  · rintro ⟨d, hd, rfl⟩
    exact scaled_mem_support p e g hd

/-- Support lower-bound order. -/
def OrderGE (f : MvPolynomial σ A) (mark : Nat) : Prop :=
  ∀ d ∈ f.support, mark ≤ exponentDegree d

/-- Frobenius power and scaled mark preserve support order exactly over any
coefficient domain. -/
theorem orderGE_power_iff
    (e mark : Nat) (g : MvPolynomial σ A) :
    OrderGE (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      OrderGE g mark := by
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  constructor
  · intro hpower d hd
    have hscaled := scaled_mem_support p e g hd
    have hbound := hpower (scaleExponent (p ^ e) d) hscaled
    rw [exponentDegree_scale] at hbound
    exact Nat.le_of_mul_le_mul_left hbound hq
  · intro hroot m hm
    rcases mem_support_power_exists_scaled p e g hm with ⟨d, hd, rfl⟩
    rw [exponentDegree_scale]
    exact Nat.mul_le_mul_left (p ^ e) (hroot d hd)

end

end FrobeniusSupportDomain
end Experimental
end PCRLean
