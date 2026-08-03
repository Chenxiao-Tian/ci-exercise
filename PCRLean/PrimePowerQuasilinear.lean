import Mathlib
import PCRLean.MarkedIdeal

/-!
# Split quasilinear forms at arbitrary prime-power level

In exponential characteristic `p`, the `e`-fold Frobenius is additive.  Hence
for `q = p^e` every split quasilinear form

`Σ (b_i^q) X_i^q`

is the single `q`-th power of the linear form `Σ b_i X_i`.  The principal
marked packet of mark `q` is therefore permissible for the actual root
hyperplane ideal.

This extends the characteristic-two quadratic root theorem to arbitrary prime
power level.  Over a perfect coefficient ring every diagonal coefficient has a
canonical root, so the split hypothesis is automatic coefficientwise; the
bundle-level gluing problem remains separate.
-/

namespace PCRLean
namespace PrimePowerQuasilinear

noncomputable section

universe u v

variable {R : Type u} {σ : Type v}
variable [CommRing R] [Fintype σ] [DecidableEq σ]
variable (p e : Nat) [ExpChar R p]

abbrev P := MvPolynomial σ R

/-- Prime-power exponent. -/
def q : Nat := p ^ e

/-- Linear Frobenius root. -/
def linearRoot (b : σ → R) : P (R := R) (σ := σ) :=
  ∑ i : σ, MvPolynomial.C (b i) * MvPolynomial.X i

/-- Split diagonal quasilinear form. -/
def form (b : σ → R) : P (R := R) (σ := σ) :=
  ∑ i : σ,
    MvPolynomial.C ((b i) ^ (q p e)) *
      (MvPolynomial.X i) ^ (q p e)

/-- The `q`-th power of a finite sum is the sum of the `q`-th powers. -/
theorem finset_sum_pow (s : Finset σ)
    (f : σ → P (R := R) (σ := σ)) :
    (∑ i ∈ s, f i) ^ (q p e) =
      ∑ i ∈ s, (f i) ^ (q p e) := by
  change iterateFrobenius (P (R := R) (σ := σ)) p e
      (∑ i ∈ s, f i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_pow]
  rfl

/-- Exact split-quasilinear root identity. -/
theorem form_eq_root_pow (b : σ → R) :
    form (R := R) p e b =
      (linearRoot (R := R) b) ^ (q p e) := by
  classical
  rw [linearRoot, form, finset_sum_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  simp [q]

/-- Actual root hyperplane ideal. -/
def rootIdeal (b : σ → R) : Ideal (P (R := R) (σ := σ)) :=
  Ideal.span {linearRoot (R := R) b}

/-- The root belongs to its actual ideal. -/
theorem root_mem_rootIdeal (b : σ → R) :
    linearRoot (R := R) b ∈ rootIdeal (R := R) b :=
  Ideal.mem_span_singleton_self _

/-- The quasilinear equation belongs to the `q`-th power of its root ideal. -/
theorem form_mem_rootIdeal_pow (b : σ → R) :
    form (R := R) p e b ∈
      (rootIdeal (R := R) b) ^ (q p e) := by
  rw [form_eq_root_pow]
  exact Ideal.pow_mem_pow (root_mem_rootIdeal (R := R) b) (q p e)

/-- A split quasilinear packet at positive prime-power mark is permissible for
its actual root hyperplane. -/
theorem markedForm_permissible
    (b : σ → R) (hq : 0 < q p e) :
    MarkedIdeal.Permissible
      (R := P (R := R) (σ := σ))
      ⟨Ideal.span {form (R := R) p e b}, q p e, hq⟩
      (rootIdeal (R := R) b) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := P (R := R) (σ := σ)) hq
    (form_mem_rootIdeal_pow (R := R) p e b)

/-- The polar expression of a split prime-power form vanishes identically. -/
theorem additive_polar_zero
    (b : σ → R)
    (x y : P (R := R) (σ := σ)) :
    (linearRoot (R := R) b + x + y) ^ (q p e) -
      (linearRoot (R := R) b + x) ^ (q p e) -
      (linearRoot (R := R) b + y) ^ (q p e) +
      (linearRoot (R := R) b) ^ (q p e) = 0 := by
  change iterateFrobenius (P (R := R) (σ := σ)) p e
      (linearRoot (R := R) b + x + y) -
    iterateFrobenius (P (R := R) (σ := σ)) p e
      (linearRoot (R := R) b + x) -
    iterateFrobenius (P (R := R) (σ := σ)) p e
      (linearRoot (R := R) b + y) +
    iterateFrobenius (P (R := R) (σ := σ)) p e
      (linearRoot (R := R) b) = 0
  simp
  ring

end

end PrimePowerQuasilinear
end PCRLean
