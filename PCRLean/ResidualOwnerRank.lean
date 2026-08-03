import Mathlib
import PCRLean.GenerationalRank

/-!
# MLEL-002: residual owner-support rank

At a pivot chart, all owners containing the pivot are terminal. The charged
union of the surviving owners is therefore contained in the old union with the
pivot erased. Cardinality is a strict well-founded rank.
-/

namespace PCRLean
namespace ResidualOwnerRank

noncomputable section

universe u

variable {ι : Type u} [DecidableEq ι]

/-- Abstract residual-union transition. -/
def Step (parent child : Finset ι) : Prop :=
  ∃ k ∈ parent, child ⊆ parent.erase k

/-- Every residual-union step strictly lowers cardinality. -/
theorem card_decreases {parent child : Finset ι}
    (h : Step parent child) : child.card < parent.card := by
  rcases h with ⟨k, hk, hsub⟩
  exact lt_of_le_of_lt (Finset.card_le_card hsub)
    (Finset.card_erase_lt_of_mem hk)

/-- No infinite ownerwise residual-coordinate branch exists. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → Finset ι,
      ∀ n, Step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending Nat.lt_wfRel.wf
    (fun n => (f n).card)
    (fun n => card_decreases (hf n))

end

end ResidualOwnerRank
end PCRLean
