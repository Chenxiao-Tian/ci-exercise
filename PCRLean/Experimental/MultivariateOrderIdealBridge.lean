import Mathlib
import PCRLean.Experimental.MultivariateFrobeniusOrderHeredity

/-!
# Multivariate order as actual ideal-power containment

Let `m = (X_i)` be the actual affine ideal of the origin.  If every supported
monomial of a polynomial has total degree at least `n`, then the polynomial
belongs to `m^n`.  Thus the support lower-bound semantics used for
multivariate order produces a genuine marked-power certificate for an actual
finite-type centre.

Combined with Frobenius order heredity, a prime-power equation `g^(p^e)` whose
root has order at least `n` belongs to `m^((p^e)*n)`.  This closes the direction
needed for marked permissibility in the affine principal rank-zero chamber.

The converse ideal-membership theorem, translation to arbitrary local points,
regular immersion, owner/passive legality and scheme-level gluing remain
separate.
-/

namespace PCRLean
namespace Experimental
namespace MultivariateOrderIdealBridge

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]

open MultivariateFrobeniusOrderHeredity
open InitialFormFrobeniusCleaning

/-- Actual coordinate ideal of the affine origin. -/
def originIdeal : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K))

/-- Every coordinate belongs to the origin ideal. -/
theorem X_mem_originIdeal (i : σ) :
    MvPolynomial.X i ∈ originIdeal (K := K) (σ := σ) :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Powers of a proper ideal form a decreasing filtration. -/
theorem pow_le_pow_of_le
    (I : Ideal (MvPolynomial σ K)) {m n : Nat} (hmn : m ≤ n) :
    I ^ n ≤ I ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  calc
    I ^ m * I ^ k ≤ I ^ m * ⊤ := mul_le_mul_left' le_top _
    _ = I ^ m := by simp

/-- One monomial belongs to the power indexed by its full total degree. -/
theorem monomial_mem_originIdeal_pow_degree
    (d : σ →₀ Nat) (a : K) :
    MvPolynomial.monomial d a ∈
      (originIdeal (K := K) (σ := σ)) ^ exponentDegree d := by
  induction d using Finsupp.induction with
  | zero => simp [exponentDegree]
  | single_add i e d hi he ih =>
      rw [exponentDegree, Finsupp.sum, Finsupp.support_single_ne_zero _ he,
        Finset.sum_insert hi, Finsupp.single_eq_same]
      rw [MvPolynomial.monomial_single_add, pow_add]
      exact Ideal.mul_mem_mul
        (Ideal.pow_mem_pow (X_mem_originIdeal (K := K) i) e) ih

/-- A monomial of degree at least `mark` belongs to the corresponding origin
ideal power. -/
theorem monomial_mem_originIdeal_pow_of_le
    (mark : Nat) (d : σ →₀ Nat) (a : K)
    (hdegree : mark ≤ exponentDegree d) :
    MvPolynomial.monomial d a ∈
      (originIdeal (K := K) (σ := σ)) ^ mark := by
  exact pow_le_pow_of_le
    (originIdeal (K := K) (σ := σ)) hdegree
    (monomial_mem_originIdeal_pow_degree (K := K) d a)

/-- Main integration theorem: the support lower-bound order predicate implies
actual marked-power containment. -/
theorem mem_originIdeal_pow_of_orderGE
    (f : MvPolynomial σ K) (mark : Nat)
    (horder : OrderGE f mark) :
    f ∈ (originIdeal (K := K) (σ := σ)) ^ mark := by
  rw [MvPolynomial.as_sum f]
  exact Ideal.sum_mem _ fun d hd =>
    monomial_mem_originIdeal_pow_of_le (K := K) mark d
      (MvPolynomial.coeff d f) (horder d hd)

/-- Prime-power order heredity compiles directly into a marked-power
certificate for the actual origin ideal. -/
theorem frobeniusPower_mem_originIdeal_pow
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (g : MvPolynomial σ K)
    (hrootOrder : OrderGE g mark) :
    g ^ (p ^ e) ∈
      (originIdeal (K := K) (σ := σ)) ^ ((p ^ e) * mark) := by
  apply mem_originIdeal_pow_of_orderGE
  exact (orderGE_power_iff p e mark g).mpr hrootOrder

end

end MultivariateOrderIdealBridge
end Experimental
end PCRLean
