import Mathlib
import PCRLean.Experimental.CausalEventLedger
import PCRLean.Experimental.PolynomialGraphMarkedTransformDebt

/-!
# Polynomial graph debt as source-conservative causal cleanup

For a graph-root block of size `q` at a positive mark `m ≤ q`, every chart has
residual ideal

`(E_k)^(q-m)`.

The key causal observation is that this is not a new birth.  The same active
source supports remain enrolled; only the internal cleanup height changes from
`q` to `q-m`.  Since `m>0`, this height strictly decreases.  The transition is
therefore an instance of `CausalEventLedger.Step.cleanup`, not of
`Step.birth`.

This file connects the exact algebraic graph-debt identity to the finite-source
termination backend and prevents chartwise exceptional residuals from being
miscounted as fresh identities.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphDebtCausalReentry

noncomputable section

universe u v w

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- Ledger state before a graph-root controlled transform. -/
def parentState
    (active : Finset (Finset Source)) (q : Nat) :
    CausalEventLedger.State (Source := Source) where
  active := active
  cleanupHeight := q

/-- Ledger state after recording the pure exceptional debt `q-mark`. -/
def childState
    (active : Finset (Finset Source)) (q mark : Nat) :
    CausalEventLedger.State (Source := Source) where
  active := active
  cleanupHeight := q - mark

/-- Source ownership is unchanged by graph-debt cleanup. -/
theorem unused_child_eq_parent
    (active : Finset (Finset Source)) (q mark : Nat) :
    (childState active q mark).unused =
      (parentState active q).unused := by
  rfl

/-- The number of active identities is unchanged. -/
theorem active_card_child_eq_parent
    (active : Finset (Finset Source)) (q mark : Nat) :
    (childState active q mark).active.card =
      (parentState active q).active.card := by
  rfl

/-- Positive mark strictly lowers the internal cleanup height. -/
theorem cleanupHeight_decreases
    (active : Finset (Finset Source))
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    (childState active q mark).cleanupHeight <
      (parentState active q).cleanupHeight := by
  change q - mark < q
  omega

/-- Exact causal classification: graph exceptional debt is a cleanup move. -/
theorem cleanupStep
    (active : Finset (Finset Source))
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    CausalEventLedger.Step
      (parentState active q)
      (childState active q mark) := by
  exact CausalEventLedger.Step.cleanup
    (unused_child_eq_parent active q mark)
    (active_card_child_eq_parent active q mark)
    (cleanupHeight_decreases active q mark hmark_pos hmark_le)

/-- The concrete finite-source rank strictly decreases. -/
theorem rank_decreases
    (active : Finset (Finset Source))
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    GenRank.Lt
      (childState active q mark).rank
      (parentState active q).rank :=
  CausalEventLedger.Step.decreases
    (cleanupStep active q mark hmark_pos hmark_le)

section GraphRealization

variable {R : Type v} [CommRing R] [IsDomain R]
variable {ι : Type w} [DecidableEq ι]

open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt

/-- One chart realization of the same source-conservative cleanup event. -/
structure ReentryCertificate
    (active : Finset (Finset Source))
    (k : ι) (q mark : Nat) where
  mark_pos : 0 < mark
  mark_le_block : mark ≤ q
  step : CausalEventLedger.Step
    (parentState active q)
    (childState active q mark)
  residualIdeal :
    transformedMarkedRootIdeal (R := R) k q mark =
      (pivotIdeal (R := R) k) ^
        (childState active q mark).cleanupHeight
  sourceSupportPreserved :
    (childState active q mark).unused =
      (parentState active q).unused
  activeIdentityCountPreserved :
    (childState active q mark).active.card =
      (parentState active q).active.card

/-- Assemble the chartwise causal-reentry certificate. -/
noncomputable def reentryCertificate
    (active : Finset (Finset Source))
    (k : ι) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    ReentryCertificate (R := R) active k q mark where
  mark_pos := hmark_pos
  mark_le_block := hmark_le
  step := cleanupStep active q mark hmark_pos hmark_le
  residualIdeal := by
    change transformedMarkedRootIdeal (R := R) k q mark =
      (pivotIdeal (R := R) k) ^ (q - mark)
    exact transformedMarkedRootIdeal_eq_pivotPower
      (R := R) k q mark
  sourceSupportPreserved := unused_child_eq_parent active q mark
  activeIdentityCountPreserved :=
    active_card_child_eq_parent active q mark

/-- Every chart realizes the same causal rank drop; chart choice cannot clone or
recharge the event. -/
theorem allCharts_sameRankDrop
    (active : Finset (Finset Source))
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q)
    (i j : ι) :
    GenRank.Lt
      (childState active q mark).rank
      (parentState active q).rank ∧
    (childState active q mark).cleanupHeight = q - mark := by
  exact ⟨rank_decreases active q mark hmark_pos hmark_le, rfl⟩

end GraphRealization

end

end PolynomialGraphDebtCausalReentry
end Experimental
end PCRLean
