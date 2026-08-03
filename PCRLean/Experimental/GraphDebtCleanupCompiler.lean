import Mathlib
import PCRLean.Experimental.ExceptionalDebtLineage

/-!
# Compile graph exceptional debt into a causal cleanup step

The arbitrary-mark graph calculation produces a residual ideal

`(E_k)^(q-m)`

with the same immutable source identity on every chart.  This file compiles
that algebraic event into the concrete finite-source termination backend.

After the source has been enrolled once, the parent and child states have the
same active support blocks and the same unused-source ledger.  The only change
is the cleanup height

`q  →  q-m`.

Because the mark is positive, `q-m < q`; hence the transition is a certified
`CausalEventLedger.Step.cleanup` and strictly lowers the concrete generation
rank.  It is not a financed birth: the source support is already used and is
therefore not disjoint from the parent ledger.

This is a local causal compiler for graph-root debt.  A general resolution
proof must still construct one immutable source event for every geometric
owner and prove that all overlap and reentry maps preserve it.
-/

namespace PCRLean
namespace Experimental
namespace GraphDebtCleanupCompiler

noncomputable section

universe u v w

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

open ExceptionalDebtLineage
open CausalEventLedger

/-- Parent state after the event source has been enrolled. -/
def parentState
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    State (Source := Source) where
  active := insert E.support baseActive
  cleanupHeight := E.block

/-- Child state after replacing the full Frobenius block by its exceptional
debt. -/
def childState
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    State (Source := Source) where
  active := insert E.support baseActive
  cleanupHeight := E.debt

@[simp] theorem active_child_eq_parent
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    (childState E baseActive).active =
      (parentState E baseActive).active := rfl

/-- The source ledger is unchanged by debt cleanup. -/
theorem unused_child_eq_parent
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    (childState E baseActive).unused =
      (parentState E baseActive).unused := by
  rfl

/-- Active support cardinality is unchanged. -/
theorem active_card_child_eq_parent
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    (childState E baseActive).active.card =
      (parentState E baseActive).active.card := by
  rfl

/-- Positive marks strictly lower the cleanup height from `q` to `q-m`. -/
theorem cleanupHeight_decreases
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    (childState E baseActive).cleanupHeight <
      (parentState E baseActive).cleanupHeight := by
  exact E.debt_lt_block

/-- Graph debt is an accepted cleanup step in the concrete causal ledger. -/
theorem cleanupStep
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    Step (parentState E baseActive) (childState E baseActive) := by
  exact Step.cleanup
    (unused_child_eq_parent E baseActive)
    (active_card_child_eq_parent E baseActive)
    (cleanupHeight_decreases E baseActive)

/-- The concrete generational rank strictly decreases. -/
theorem rank_decreases
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    GenRank.Lt
      (childState E baseActive).rank
      (parentState E baseActive).rank :=
  Step.decreases (cleanupStep E baseActive)

/-- The event support is already used in the parent state. -/
theorem support_not_disjoint_parent_used
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    ¬ Disjoint E.support (parentState E baseActive).used := by
  have hparent : parentState E baseActive =
      ExceptionalDebtLineage.enroll E
        { active := baseActive, cleanupHeight := E.block } := by
    rfl
  rw [hparent]
  exact ExceptionalDebtLineage.support_not_disjoint_used_after_enroll
    E { active := baseActive, cleanupHeight := E.block }

/-- The same source support cannot satisfy the fresh-birth disjointness gate
at the cleanup parent. -/
theorem not_fresh_birth_same_support
    (E : Event (Source := Source))
    (baseActive : Finset (Finset Source)) :
    ¬ Disjoint E.support (parentState E baseActive).used :=
  support_not_disjoint_parent_used E baseActive

section GraphAlgebra

variable {R : Type v} [CommRing R] [IsDomain R]
variable {ι : Type w} [DecidableEq ι]

open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt

/-- Every chart residual ideal is the exceptional pivot raised to the cleanup
height of the compiled child state. -/
theorem graphResidualIdeal_eq_childHeight
    (source : Source) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_le : mark ≤ q)
    (baseActive : Finset (Finset Source)) (k : ι) :
    transformedMarkedRootIdeal (R := R) k q mark =
      (pivotIdeal (R := R) k) ^
        (childState
          (graphEvent source q mark hmark_pos hmark_le)
          baseActive).cleanupHeight := by
  simpa [childState] using
    (graphResidualIdeal_eq_eventDebt
      (R := R) source q mark hmark_pos hmark_le k)

/-- At the exact mark the cleanup child has height zero. -/
theorem exactMark_childHeight_zero
    (source : Source) (q : Nat) (hq : 0 < q)
    (baseActive : Finset (Finset Source)) :
    (childState (graphEvent source q q hq le_rfl)
      baseActive).cleanupHeight = 0 := by
  simp [childState, graphEvent, Event.debt]

end GraphAlgebra

end

end GraphDebtCleanupCompiler
end Experimental
end PCRLean
