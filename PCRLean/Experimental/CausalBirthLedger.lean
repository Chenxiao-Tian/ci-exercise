import Mathlib
import PCRLean.GenerationalRank

/-!
# Experimental no-recharge causal birth ledger

A finite ancestor-source set is equipped with a historical ledger of every
source that has ever financed a geometric birth.  The ledger never shrinks.
A genuinely fresh birth must strictly increase its cardinality.  Every other
accepted transition must keep the ledger fixed and strictly decrease a local
natural-number rank.

The lexicographic rank `(unused historical sources, local rank)` is well
founded.  Consequently no infinite execution can satisfy the no-recharge
classification.  This theorem does not construct the source ledger from an
arbitrary blowup sequence; that is the geometric birth-realization obligation.
-/

namespace PCRLean
namespace Experimental
namespace CausalBirthLedger

noncomputable section

universe u

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- Historical source ledger together with the rank for dependent local work. -/
structure State where
  used : Finset Source
  localRank : Nat
  deriving DecidableEq, Repr

/-- Concrete two-level termination rank. -/
abbrev Rank := Nat × Nat

/-- Number of ancestor sources never previously charged. -/
def unusedCount (s : State (Source := Source)) : Nat :=
  Fintype.card Source - s.used.card

/-- Compiled ledger rank. -/
def rank (s : State (Source := Source)) : Rank :=
  (unusedCount s, s.localRank)

/-- Strict lexicographic order on ledger ranks. -/
def RankLt : Rank → Rank → Prop :=
  Prod.Lex Nat.lt Nat.lt

/-- The ledger rank order is well founded. -/
theorem rankLt_wellFounded : WellFounded RankLt :=
  WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf

/-- Accepted transitions.  Fresh births monotonically enlarge the historical
ledger; dependent work leaves it fixed and decreases the local rank. -/
inductive Step : State (Source := Source) → State (Source := Source) → Prop
  | freshBirth (parent child)
      (hsubset : parent.used ⊆ child.used)
      (hcard : parent.used.card < child.used.card) : Step parent child
  | localDrop (parent child)
      (hused : child.used = parent.used)
      (hrank : child.localRank < parent.localRank) : Step parent child

/-- A fresh nonempty support disjoint from the historical ledger strictly
increases ledger cardinality. -/
theorem card_union_fresh_lt
    (used support : Finset Source)
    (hdisj : Disjoint used support)
    (hnew : support.Nonempty) :
    used.card < (used ∪ support).card := by
  rw [Finset.card_union_of_disjoint hdisj]
  exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hnew)

/-- Enrolling a genuinely fresh support is an accepted birth transition. -/
theorem enrollFreshSupport_step
    (parent : State (Source := Source))
    (support : Finset Source)
    (hdisj : Disjoint parent.used support)
    (hnew : support.Nonempty)
    (newLocalRank : Nat) :
    Step parent
      ⟨parent.used ∪ support, newLocalRank⟩ := by
  apply Step.freshBirth
  · exact Finset.subset_union_left
  · exact card_union_fresh_lt parent.used support hdisj hnew

/-- Historical enrollment is irreversible: every previously used source
remains used after a fresh birth. -/
theorem used_mono_of_step {parent child : State (Source := Source)}
    (h : Step parent child) : parent.used ⊆ child.used := by
  cases h with
  | freshBirth _ _ hsubset _ => exact hsubset
  | localDrop _ _ hused _ => simpa [hused]

/-- Every accepted transition strictly lowers the concrete ledger rank. -/
theorem step_decreases {parent child : State (Source := Source)}
    (h : Step parent child) : RankLt (rank child) (rank parent) := by
  cases h with
  | freshBirth parent child hsubset hcard =>
      apply Prod.Lex.left
      · exact child.localRank
      · exact parent.localRank
      · have hparent : parent.used.card ≤ Fintype.card Source := by
          simpa using Finset.card_le_card
            (show parent.used ⊆ (Finset.univ : Finset Source) by simp)
        have hchild : child.used.card ≤ Fintype.card Source := by
          simpa using Finset.card_le_card
            (show child.used ⊆ (Finset.univ : Finset Source) by simp)
        simp only [rank, unusedCount]
        omega
  | localDrop parent child hused hrank =>
      apply Prod.Lex.right
      · simp [rank, unusedCount, hused]
      · exact hrank

/-- There is no infinite no-recharge execution. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → State (Source := Source),
      ∀ n, Step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending rankLt_wellFounded
    (fun n => rank (f n))
    (fun n => step_decreases (hf n))

/-- The historical ledger cannot support infinitely many genuinely fresh
births even if local ranks are reset at each birth. -/
theorem no_infinite_fresh_births :
    ¬ ∃ f : Nat → State (Source := Source),
      ∀ n, ∃ hsubset : (f n).used ⊆ (f (n + 1)).used,
        (f n).used.card < (f (n + 1)).used.card := by
  rintro ⟨f, hf⟩
  have hstep : ∀ n, Step (f n) (f (n + 1)) := by
    intro n
    rcases hf n with ⟨hsubset, hcard⟩
    exact Step.freshBirth _ _ hsubset hcard
  exact no_infinite_execution ⟨f, hstep⟩

end

end CausalBirthLedger
end Experimental
end PCRLean
