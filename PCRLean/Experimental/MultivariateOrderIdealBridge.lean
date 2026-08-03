import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.Experimental.MultivariateFrobeniusOrderHeredity

/-!
# Multivariate order as actual ideal-power containment

Let `m = (X_i)` be the actual affine ideal of the origin. Mathlib proves the
exact monomial-ideal theorem

`f ∈ m^n ↔ ∀ d ∈ support(f), n ≤ degree(d)`.

The support lower-bound semantics used for multivariate order is precisely the
right-hand side. Thus pointwise order is not merely a combinatorial proxy: it
is exactly actual ideal-power containment.

Combined with Frobenius order heredity, a prime-power equation `g^(p^e)` whose
root has order at least `n` belongs to `m^((p^e)*n)`. This closes marked
permissibility for the affine principal rank-zero chamber.

Translation to arbitrary local points is handled separately. Regular immersion,
owner/passive legality and scheme-level gluing remain open beyond this chamber.
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
  MvPolynomial.idealOfVars σ K

/-- Our exponent-degree notation agrees with mathlib's `Finsupp.degree`. -/
theorem exponentDegree_eq_degree (d : σ →₀ Nat) :
    exponentDegree d = Finsupp.degree d := by
  rfl

/-- Every coordinate belongs to the origin ideal. -/
theorem X_mem_originIdeal (i : σ) :
    MvPolynomial.X i ∈ originIdeal (K := K) (σ := σ) :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Exact equivalence between support order and actual ideal-power membership. -/
theorem mem_originIdeal_pow_iff_orderGE
    (f : MvPolynomial σ K) (mark : Nat) :
    f ∈ (originIdeal (K := K) (σ := σ)) ^ mark ↔
      OrderGE f mark := by
  rw [originIdeal, MvPolynomial.mem_pow_idealOfVars_iff]
  exact forall₂_congr fun d hd => by
    rw [exponentDegree_eq_degree]

/-- Support order compiles into actual marked-power containment. -/
theorem mem_originIdeal_pow_of_orderGE
    (f : MvPolynomial σ K) (mark : Nat)
    (horder : OrderGE f mark) :
    f ∈ (originIdeal (K := K) (σ := σ)) ^ mark :=
  (mem_originIdeal_pow_iff_orderGE f mark).mpr horder

/-- Actual ideal-power membership recovers the support-order predicate. -/
theorem orderGE_of_mem_originIdeal_pow
    (f : MvPolynomial σ K) (mark : Nat)
    (hmem : f ∈ (originIdeal (K := K) (σ := σ)) ^ mark) :
    OrderGE f mark :=
  (mem_originIdeal_pow_iff_orderGE f mark).mp hmem

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
