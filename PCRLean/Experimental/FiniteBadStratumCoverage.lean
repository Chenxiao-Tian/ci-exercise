import Mathlib

/-!
# Choice-free coverage by the full bad-stratum set

The clean-or-defect split should not select an arbitrary first bad stratum.
Given a finite intersection arrangement and a geometric gate `Good`, retain the
entire finite set of failing strata.  This set is intrinsic under every
permutation preserving the arrangement and the gate.

The file proves exact coverage:

* the bad set is empty exactly when every stratum is good;
* the bad set is nonempty exactly when a bad stratum exists; and
* the arrangement enters either the clean branch or a nonempty finite defect
  layer.

Geometry must still instantiate `Good` with regularity, active/passive/SNC
legality and nonidentity, and must construct a strict successor from the defect
layer.
-/

namespace PCRLean
namespace Experimental
namespace FiniteBadStratumCoverage

noncomputable section

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- All failing strata, retained without choosing one point. -/
def badStrata
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good] :
    Finset α :=
  strata.filter fun a => ¬ Good a

@[simp] theorem mem_badStrata_iff
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good]
    (a : α) :
    a ∈ badStrata strata Good ↔ a ∈ strata ∧ ¬ Good a := by
  simp [badStrata]

/-- The defect layer is empty precisely in the clean chamber. -/
theorem badStrata_eq_empty_iff
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good] :
    badStrata strata Good = ∅ ↔ ∀ a ∈ strata, Good a := by
  simp [badStrata]

/-- A nonempty defect layer is exactly an existential failure witness, but the
output remains the full finite set rather than an arbitrary chosen witness. -/
theorem badStrata_nonempty_iff
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good] :
    (badStrata strata Good).Nonempty ↔
      ∃ a ∈ strata, ¬ Good a := by
  constructor
  · rintro ⟨a, ha⟩
    have h := (mem_badStrata_iff strata Good a).mp ha
    exact ⟨a, h.1, h.2⟩
  · rintro ⟨a, ha, hbad⟩
    exact ⟨a, (mem_badStrata_iff strata Good a).mpr ⟨ha, hbad⟩⟩

/-- Exact finite coverage of the clean and defect chambers. -/
inductive Coverage
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good] : Type u where
  | clean (allGood : ∀ a ∈ strata, Good a)
  | defect (nonempty : (badStrata strata Good).Nonempty)

/-- The choice-free clean-or-defect classifier. -/
noncomputable def classify
    (strata : Finset α) (Good : α → Prop) [DecidablePred Good] :
    Coverage strata Good := by
  classical
  by_cases h : ∀ a ∈ strata, Good a
  · exact Coverage.clean h
  · apply Coverage.defect
    rw [badStrata_nonempty_iff]
    by_contra hnone
    apply h
    intro a ha
    by_contra hbad
    exact hnone ⟨a, ha, hbad⟩

end

end FiniteBadStratumCoverage
end Experimental
end PCRLean
