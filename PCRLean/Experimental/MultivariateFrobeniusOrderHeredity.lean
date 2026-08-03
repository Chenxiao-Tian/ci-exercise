import Mathlib
import PCRLean.Experimental.PerfectFrobeniusRankZeroEscape
import PCRLean.Experimental.InitialFormFrobeniusCleaning

/-!
# Multivariate Frobenius order heredity

Instead of defining the order of a multivariate polynomial by a minimum, use
the equivalent lower-bound predicate: every supported monomial has total degree
at least the mark.  This makes the zero polynomial automatically have infinite
order and avoids a special value in the rank.

In characteristic `p`, raising to `q = p^e` scales every supported exponent by
`q` and raises its coefficient to the `q`-th power.  Since the coefficient ring
is a field, no supported term disappears.  Therefore

`ord_0(g^q) >= q*m  ↔  ord_0(g) >= m`.

After multivariate translation the same equivalence holds at every rational
point.  This is the multivariable principal affine singular-locus heredity
bridge for Frobenius mark compression.  General local rings and nonprincipal
Rees presentations remain separate.
-/

namespace PCRLean
namespace Experimental
namespace MultivariateFrobeniusOrderHeredity

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p]

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
    (e : Nat) (g : MvPolynomial σ K) :
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

/-- Every supported root monomial survives at its scaled exponent in the
Frobenius power. -/
theorem scaled_mem_support
    (e : Nat) (g : MvPolynomial σ K)
    {d : σ →₀ Nat} (hd : d ∈ g.support) :
    scaleExponent (p ^ e) d ∈ (g ^ (p ^ e)).support := by
  classical
  rw [MvPolynomial.mem_support_iff, frobeniusPower_expansion]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp [MvPolynomial.mem_support_iff.mp hd]
  · intro b hb hbd
    rw [if_neg]
    intro hscale
    apply hbd
    exact scaleExponent_injective (σ := σ) (p ^ e)
      (pow_pos (Fact.out : p.Prime).pos e) hscale
  · intro hdnot
    exact (hdnot hd).elim

/-- Every supported monomial of the Frobenius power is the scaled image of a
supported root monomial. -/
theorem mem_support_power_exists_scaled
    (e : Nat) (g : MvPolynomial σ K)
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

/-- Exact support characterization of a prime-power Frobenius power. -/
theorem mem_support_power_iff
    (e : Nat) (g : MvPolynomial σ K) (m : σ →₀ Nat) :
    m ∈ (g ^ (p ^ e)).support ↔
      ∃ d ∈ g.support, scaleExponent (p ^ e) d = m := by
  constructor
  · exact mem_support_power_exists_scaled p e g
  · rintro ⟨d, hd, rfl⟩
    exact scaled_mem_support p e g hd

/-- Order-at-the-origin lower-bound predicate. -/
def OrderGE (f : MvPolynomial σ K) (mark : Nat) : Prop :=
  ∀ d ∈ f.support, mark ≤ exponentDegree d

/-- Frobenius power and mark compression preserve multivariate order exactly. -/
theorem orderGE_power_iff
    (e mark : Nat) (g : MvPolynomial σ K) :
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

/-- Multivariate translation by a rational point. -/
def translate (a : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i)

/-- Pointwise multivariate marked singularity. -/
def AtPointOrderGE (a : σ → K)
    (f : MvPolynomial σ K) (mark : Nat) : Prop :=
  OrderGE (translate a f) mark

/-- Frobenius mark compression preserves the pointwise order condition in every
multivariate affine chart. -/
theorem atPointOrderGE_power_iff
    (e mark : Nat) (a : σ → K) (g : MvPolynomial σ K) :
    AtPointOrderGE a (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      AtPointOrderGE a g mark := by
  unfold AtPointOrderGE
  rw [map_pow]
  exact orderGE_power_iff p e mark (translate a g)

end

end MultivariateFrobeniusOrderHeredity
end Experimental
end PCRLean
