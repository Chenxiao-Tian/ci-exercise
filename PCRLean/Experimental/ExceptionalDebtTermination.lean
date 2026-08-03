import Mathlib
import PCRLean.Experimental.ExceptionalDebtLedger

/-!
# Well-founded termination for exceptional-debt registration

For a finite ancestor-source type, a state records one Frobenius block `q` and
a finite ledger of debt keys in that block.  The rank is

`(q, card(Source) * q - ledger.card)`.

An accepted transition is either:

* a strict drop of the Frobenius block, with the new ledger rebuilt; or
* registration of one genuinely fresh key in the same block.

The first transition lowers the primary rank.  The second increases ledger
cardinality exactly once and therefore lowers remaining capacity.  The induced
transition relation is well founded and admits no infinite execution.

In the geometric algorithm the block drop must be justified by Frobenius-root
or presentation-degree descent.  This file supplies the debt component of the
termination compiler, not that geometric classification.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalDebtTermination

noncomputable section

universe u

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- State of one debt-registration block. -/
structure State (Source : Type u) [Fintype Source] [DecidableEq Source] where
  block : Nat
  ledger : ExceptionalDebtLedger.Ledger Source block

/-- Lexicographic debt rank. -/
def rank (s : State Source) : Nat × Nat :=
  (s.block, Fintype.card Source * s.block - s.ledger.card)

/-- Accepted transitions, oriented from child to parent. -/
inductive Step : State Source → State Source → Prop
  | blockDrop {child parent : State Source}
      (hdrop : child.block < parent.block) : Step child parent
  | fresh {q : Nat}
      {L : ExceptionalDebtLedger.Ledger Source q}
      {key : ExceptionalDebtLedger.DebtKey Source q}
      (hfresh : key ∉ L) :
      Step ⟨q, ExceptionalDebtLedger.register L key⟩ ⟨q, L⟩

/-- Rank relation. -/
def RankLt : Nat × Nat → Nat × Nat → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- The rank relation is well founded. -/
theorem rankLt_wellFounded : WellFounded RankLt := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf

/-- Every accepted debt transition strictly decreases rank. -/
theorem step_decreases
    {child parent : State Source}
    (h : Step child parent) :
    RankLt (rank child) (rank parent) := by
  cases h with
  | blockDrop hdrop =>
      exact Prod.Lex.left _ _ hdrop
  | @fresh q L key hfresh =>
      apply Prod.Lex.right
      rw [rank, rank]
      simp only
      have hcard := ExceptionalDebtLedger.card_register_of_fresh
        L key hfresh
      have hcap := ExceptionalDebtLedger.ledger_card_le_capacity L
      have hnewcap := ExceptionalDebtLedger.ledger_card_le_capacity
        (ExceptionalDebtLedger.register L key)
      simp only [State.block, State.ledger]
      rw [hcard]
      omega

/-- The accepted transition relation is well founded. -/
theorem step_wellFounded : WellFounded (Step (Source := Source)) := by
  exact Subrelation.wf step_decreases rankLt_wellFounded

/-- No infinite debt-registration execution exists. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → State Source,
      ∀ n, Step (f (n + 1)) (f n) := by
  intro h
  rcases h with ⟨f, hf⟩
  exact (step_wellFounded (Source := Source)).not_lt_min
    (f 0) (f 1) (hf 0)

end

end ExceptionalDebtTermination
end Experimental
end PCRLean
