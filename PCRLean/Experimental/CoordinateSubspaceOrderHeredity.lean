import Mathlib
import PCRLean.CoordinateBlowupChart
import PCRLean.Experimental.MultivariateFrobeniusOrderHeredity

/-!
# Positive-dimensional coordinate-centre order heredity

Split the affine variables into passive variables `α` and centre variables
`ι`.  The centre degree of a monomial is the sum of its exponents only in the
centre variables.  This is the normal order along the positive-dimensional
coordinate subspace cut out by all centre variables.

The file proves three bridges.

1. Every monomial belongs to the power of the actual coordinate-centre ideal
   indexed by its centre degree.
2. A support lower bound on centre degree therefore gives actual marked-power
   containment in that coherent ideal.
3. Prime-power Frobenius scales centre degree and the mark exactly, so
   Frobenius root compression preserves the centre-order condition.

This extends the earlier rational-point theorem to a genuine
positive-dimensional regular coordinate centre.  It does not prove the
converse ideal-membership characterization, arbitrary linear-frame transport,
localization at nonrational scheme points, passive Tor safety, boundary SNC, or
hereditary controlled transforms.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateSubspaceOrderHeredity

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype ι] [DecidableEq ι]

abbrev Variables := CoordinateBlowupChart.Variables (α := α) (ι := ι)
abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

open MultivariateFrobeniusOrderHeredity

/-- Total exponent only in the coordinates normal to the centre. -/
def centreDegree (d : Variables (α := α) (ι := ι) →₀ Nat) : Nat :=
  ∑ i : ι, d (Sum.inr i)

/-- Centre degree is additive. -/
theorem centreDegree_add
    (d e : Variables (α := α) (ι := ι) →₀ Nat) :
    centreDegree (d + e) = centreDegree d + centreDegree e := by
  classical
  simp [centreDegree, Finset.sum_add_distrib]

/-- A passive singleton contributes no normal degree. -/
@[simp] theorem centreDegree_single_passive
    (a : α) (n : Nat) :
    centreDegree (Finsupp.single (Sum.inl a) n :
      Variables (α := α) (ι := ι) →₀ Nat) = 0 := by
  classical
  simp [centreDegree]

/-- A centre singleton contributes exactly its exponent. -/
@[simp] theorem centreDegree_single_centre
    (i : ι) (n : Nat) :
    centreDegree (Finsupp.single (Sum.inr i) n :
      Variables (α := α) (ι := ι) →₀ Nat) = n := by
  classical
  simp [centreDegree]

/-- Scaling an exponent vector scales its centre degree. -/
theorem centreDegree_scale
    (q : Nat) (d : Variables (α := α) (ι := ι) →₀ Nat) :
    centreDegree (scaleExponent q d) = q * centreDegree d := by
  classical
  simp [centreDegree, scaleExponent, Finset.mul_sum]

/-- Every centre coordinate belongs to the actual coordinate-centre ideal. -/
theorem centreVar_mem (i : ι) :
    CoordinateBlowupChart.centreVar (R := K) (α := α) (ι := ι) i ∈
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) := by
  rw [CoordinateBlowupChart.centreIdeal]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Powers of an ideal form a decreasing filtration. -/
theorem pow_le_pow_of_le
    (I : Ideal (P (K := K) (α := α) (ι := ι)))
    {m n : Nat} (hmn : m ≤ n) :
    I ^ n ≤ I ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  calc
    I ^ m * I ^ k ≤ I ^ m * ⊤ := mul_le_mul_left' le_top _
    _ = I ^ m := by simp

/-- One monomial belongs to the power indexed by its full normal degree. -/
theorem monomial_mem_centreIdeal_pow_centreDegree
    (d : Variables (α := α) (ι := ι) →₀ Nat) (a : K) :
    MvPolynomial.monomial d a ∈
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) ^ centreDegree d := by
  classical
  induction d using Finsupp.induction with
  | zero => simp [centreDegree]
  | single_add s n d hs hn ih =>
      cases s with
      | inl x =>
          have hdeg :
              centreDegree
                  (Finsupp.single (Sum.inl x) n + d :
                    Variables (α := α) (ι := ι) →₀ Nat) =
                centreDegree d := by
            simp [centreDegree_add]
          rw [hdeg, MvPolynomial.monomial_single_add]
          exact
            ((CoordinateBlowupChart.centreIdeal
              (R := K) (α := α) (ι := ι)) ^ centreDegree d).mul_mem_left _ ih
      | inr i =>
          have hdeg :
              centreDegree
                  (Finsupp.single (Sum.inr i) n + d :
                    Variables (α := α) (ι := ι) →₀ Nat) =
                n + centreDegree d := by
            simp [centreDegree_add]
          rw [hdeg, MvPolynomial.monomial_single_add, pow_add]
          exact Ideal.mul_mem_mul
            (Ideal.pow_mem_pow (centreVar_mem (K := K) (α := α) i) n) ih

/-- Support lower bound for normal order along the centre. -/
def CentreOrderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) : Prop :=
  ∀ d ∈ f.support, mark ≤ centreDegree d

/-- A centre-order lower bound gives actual marked-power containment in the
positive-dimensional coordinate-centre ideal. -/
theorem mem_centreIdeal_pow_of_centreOrderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat)
    (horder : CentreOrderGE f mark) :
    f ∈ (CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι)) ^ mark := by
  rw [MvPolynomial.as_sum f]
  exact Ideal.sum_mem _ fun d hd =>
    pow_le_pow_of_le
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι))
      (horder d hd)
      (monomial_mem_centreIdeal_pow_centreDegree
        (K := K) (α := α) d (MvPolynomial.coeff d f))

/-- Frobenius power and scaled mark preserve centre order exactly. -/
theorem centreOrderGE_power_iff
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (g : P (K := K) (α := α) (ι := ι)) :
    CentreOrderGE (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      CentreOrderGE g mark := by
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  constructor
  · intro hpower d hd
    have hscaled := scaled_mem_support p e g hd
    have hbound := hpower (scaleExponent (p ^ e) d) hscaled
    rw [centreDegree_scale] at hbound
    exact Nat.le_of_mul_le_mul_left hbound hq
  · intro hroot m hm
    rcases mem_support_power_exists_scaled p e g hm with ⟨d, hd, rfl⟩
    rw [centreDegree_scale]
    exact Nat.mul_le_mul_left (p ^ e) (hroot d hd)

/-- A root centre-order certificate compiles to marked-power containment for
its prime-power equation along the same positive-dimensional centre. -/
theorem frobeniusPower_mem_centreIdeal_pow
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (g : P (K := K) (α := α) (ι := ι))
    (hrootOrder : CentreOrderGE g mark) :
    g ^ (p ^ e) ∈
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) ^ ((p ^ e) * mark) := by
  apply mem_centreIdeal_pow_of_centreOrderGE
  exact (centreOrderGE_power_iff p e mark g).mpr hrootOrder

end

end CoordinateSubspaceOrderHeredity
end Experimental
end PCRLean
