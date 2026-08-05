import Mathlib

/-!
# Finite arrangement-completion universe

Given finitely many finite strata, every source-enriched intersection stratum
is a subset of the finite union of their point sets.  The powerset of this
finite union is therefore a finite ambient search space containing all original
strata and closed under binary intersection.

The construction is deliberately an over-approximation: it proves finiteness
of the candidate completion space, not that every subset is geometrically a
stratum.  Scheme-theoretic effectivity, regularity, source labels, and blowup
serialization remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace FiniteArrangementCompletion

noncomputable section

universe u

variable {α : Type u} [DecidableEq α]

/-- The finite point universe carried by a finite family of finite strata. -/
def pointUniverse (family : Finset (Finset α)) : Finset α :=
  family.biUnion id

/-- A finite over-approximation to the full intersection completion. -/
def completionUniverse (family : Finset (Finset α)) : Finset (Finset α) :=
  (pointUniverse family).powerset

/-- Every original stratum lies in the finite completion universe. -/
theorem original_mem_completion
    {family : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ family) :
    S ∈ completionUniverse family := by
  rw [completionUniverse, Finset.mem_powerset]
  intro x hx
  rw [pointUniverse, Finset.mem_biUnion]
  exact ⟨S, hS, hx⟩

/-- The completion universe is closed under binary intersection. -/
theorem inter_mem_completion
    {family : Finset (Finset α)} {A B : Finset α}
    (hA : A ∈ completionUniverse family)
    (hB : B ∈ completionUniverse family) :
    A ∩ B ∈ completionUniverse family := by
  rw [completionUniverse, Finset.mem_powerset] at hA hB ⊢
  exact (Finset.inter_subset_left.trans hA)

/-- Every finite iterated intersection of original strata remains inside one
fixed finite search universe; no new point label can be born by intersection
completion. -/
theorem subset_pointUniverse_of_mem_completion
    {family : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ completionUniverse family) :
    S ⊆ pointUniverse family := by
  simpa [completionUniverse] using hS

end

end FiniteArrangementCompletion
end Experimental
end PCRLean
