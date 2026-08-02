import Mathlib
import PCRLean.GenerationalRank

namespace PCRLean
namespace SourcePartition

variable {α : Type*} [DecidableEq α]

/-- Merging two source blocks preserves disjointness from every third block
that was disjoint from both parents. -/
theorem merge_preserves_disjoint {A B C : Finset α}
    (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Disjoint (A ∪ B) C := by
  rw [Finset.disjoint_left] at hAC hBC ⊢
  intro x hx hC
  simp only [Finset.mem_union] at hx
  rcases hx with hA | hB
  · exact hAC hA hC
  · exact hBC hB hC

/-- The union child of two nonempty parents is nonempty. -/
theorem merge_child_nonempty {A B : Finset α}
    (hA : A.Nonempty) : (A ∪ B).Nonempty := by
  exact hA.mono Finset.subset_union_left

/-- A source atom already active in a third block cannot enter the union child
when the original partition was pairwise disjoint. -/
theorem no_clone_into_merge {A B C : Finset α}
    (hAC : Disjoint A C) (hBC : Disjoint B C)
    {x : α} (hxC : x ∈ C) : x ∉ A ∪ B := by
  intro hx
  exact (Finset.disjoint_left.mp (merge_preserves_disjoint hAC hBC)) hx hxC

/-- Consuming `r ≥ 2` parents and inserting one child lowers the active count
by at least one. -/
theorem merge_lowers_active_count {A r : Nat} (hr : 2 ≤ r) (hA : r ≤ A) :
    A - r + 1 < A := by
  omega

/-- A protocol that permits cloning admits a self-loop and therefore an
infinite run.  This is the precise finite-source split/clone no-go. -/
inductive CloneStep : Nat → Nat → Prop
  | clone (n : Nat) : CloneStep n n

/-- The constant path is an infinite clone path. -/
theorem clone_allows_infinite_path (n : Nat) :
    ∃ f : Nat → Nat, ∀ k, CloneStep (f k) (f (k + 1)) := by
  refine ⟨fun _ => n, ?_⟩
  intro k
  exact CloneStep.clone n

/-- Consequently no irreflexive strict rank can certify every clone step. -/
theorem no_rank_strict_on_clones
    {β : Type*} (rank : Nat → β) (lt : β → β → Prop)
    (hirr : ∀ x, ¬ lt x x) :
    ¬ (∀ {a b}, CloneStep a b → lt (rank b) (rank a)) := by
  intro h
  exact hirr (rank 0) (h (CloneStep.clone 0))

end SourcePartition
end PCRLean
