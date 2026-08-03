import Mathlib
import PCRLean.Experimental.InitialFormFrobeniusCleaning

/-!
# Finite termination of initial-form Frobenius cleaning

A lowest homogeneous initial form and its strictly higher remainder have
disjoint monomial supports. If the initial form is nonzero, removing it by the
canonical Frobenius cleaning leaves a polynomial whose support is a strict
subset of the original support. Hence support cardinality is a well-founded
rank for repeated cleaning.

This gives a finite cleaning theorem without requiring an a priori degree bound.
It is still an affine polynomial statement; geometric re-preparation and
compatibility with controlled transforms remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace InitialFormCleaningTermination

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

open InitialFormFrobeniusCleaning

/-- Initial and higher-order supports are disjoint. -/
theorem support_disjoint
    {f : MvPolynomial σ K} {n : Nat}
    (D : InitialDecomposition f n) :
    Disjoint D.initial.support D.remainder.support := by
  rw [Finset.disjoint_left]
  intro m hmInitial hmRemainder
  have hi := D.initial_homogeneous m hmInitial
  have hr := D.remainder_higher m hmRemainder
  omega

/-- Every remainder monomial survives in the original polynomial. -/
theorem remainder_support_subset
    {f : MvPolynomial σ K} {n : Nat}
    (D : InitialDecomposition f n) :
    D.remainder.support ⊆ f.support := by
  intro m hmRemainder
  have hnotInitial : m ∉ D.initial.support := by
    exact (Finset.disjoint_right.mp (support_disjoint D)) hmRemainder
  have hcoeffInitial : MvPolynomial.coeff m D.initial = 0 := by
    by_contra hne
    exact hnotInitial (MvPolynomial.mem_support_iff.mpr hne)
  have hcoeffRemainder : MvPolynomial.coeff m D.remainder ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmRemainder
  rw [D.equation, MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
    hcoeffInitial, zero_add]
  exact hcoeffRemainder

/-- Every initial monomial survives in the original polynomial. -/
theorem initial_support_subset
    {f : MvPolynomial σ K} {n : Nat}
    (D : InitialDecomposition f n) :
    D.initial.support ⊆ f.support := by
  intro m hmInitial
  have hnotRemainder : m ∉ D.remainder.support :=
    (Finset.disjoint_left.mp (support_disjoint D)) hmInitial
  have hcoeffRemainder : MvPolynomial.coeff m D.remainder = 0 := by
    by_contra hne
    exact hnotRemainder (MvPolynomial.mem_support_iff.mpr hne)
  have hcoeffInitial : MvPolynomial.coeff m D.initial ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmInitial
  rw [D.equation, MvPolynomial.mem_support_iff, MvPolynomial.coeff_add,
    hcoeffRemainder, add_zero]
  exact hcoeffInitial

/-- A nonzero initial form makes the remainder support a strict subset of the
original support. -/
theorem remainder_support_ssubset
    {f : MvPolynomial σ K} {n : Nat}
    (D : InitialDecomposition f n)
    (hinitial : D.initial ≠ 0) :
    D.remainder.support ⊂ f.support := by
  have hsubset := remainder_support_subset D
  have hne : D.remainder.support ≠ f.support := by
    obtain ⟨m, hmInitial⟩ := MvPolynomial.support_nonempty.mpr hinitial
    have hmOriginal : m ∈ f.support := initial_support_subset D hmInitial
    have hmNotRemainder : m ∉ D.remainder.support :=
      (Finset.disjoint_left.mp (support_disjoint D)) hmInitial
    intro heq
    apply hmNotRemainder
    rw [heq]
    exact hmOriginal
  exact lt_of_le_of_ne hsubset hne

/-- Frobenius cleaning of a nonzero initial form strictly lowers support
cardinality. -/
theorem cleaned_support_card_lt
    {f : MvPolynomial σ K} {n : Nat}
    (D : InitialDecomposition f n)
    (hrank : D.RankZero)
    (hinitial : D.initial ≠ 0) :
    (f - (D.root p) ^ p).support.card < f.support.card := by
  rw [D.cleaned_eq_remainder p hrank]
  exact Finset.card_lt_card (remainder_support_ssubset D hinitial)

/-- One certified initial-form cleaning transition. -/
def CleaningStep
    (parent child : MvPolynomial σ K) : Prop :=
  ∃ n : Nat, ∃ D : InitialDecomposition parent n,
    D.RankZero ∧ D.initial ≠ 0 ∧
      child = parent - (D.root p) ^ p

/-- Every certified cleaning step decreases monomial support cardinality. -/
theorem cleaningStep_decreases
    {parent child : MvPolynomial σ K}
    (h : CleaningStep p parent child) :
    child.support.card < parent.support.card := by
  rcases h with ⟨n, D, hrank, hinitial, rfl⟩
  exact cleaned_support_card_lt p D hrank hinitial

/-- There is no infinite chain of certified rank-zero initial-form cleanings. -/
theorem no_infinite_cleaning_chain :
    ¬ ∃ f : Nat → MvPolynomial σ K,
      ∀ n, CleaningStep p (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending Nat.lt_wfRel.wf
    (fun n => (f n).support.card)
    (fun n => cleaningStep_decreases p (hf n))

end

end InitialFormCleaningTermination
end Experimental
end PCRLean
