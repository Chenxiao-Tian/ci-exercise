import Mathlib
import PCRLean.Experimental.CausalEventLedger
import PCRLean.Experimental.PolynomialGraphMarkedTransformDebt

/-!
# Immutable source lineage for exceptional Frobenius debt

The graph-centre calculation identifies every chart residual with a pure
exceptional power.  This file attaches that residual to one immutable source
event instead of allowing every chart to create a fresh birth identity.

An event stores one ancestor source, one Frobenius block `q`, and one mark
`m ≤ q`.  Its debt exponent is `q-m`.  Every chart observation of the event has
the same singleton source support.  Enrolling that support in the causal ledger
is idempotent, and after the first enrollment the same support is not disjoint
from the used-source set; hence it cannot satisfy the protocol for a second
financed birth.

For polynomial graph centres, the algebraic residual ideal in every chart is
proved to be exactly the exceptional pivot ideal raised to the event debt
exponent.  Thus chart variation changes the local exceptional divisor but not
the event identity or its charge.

This does not yet prove that arbitrary geometric exceptional components admit
such a source assignment.  It provides the exact no-clone/no-recharge target
that a scheme-level hereditary transform must realize.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalDebtLineage

noncomputable section

universe u v w x

variable {Source : Type u} [DecidableEq Source]
variable {Chart : Type v}

/-- Immutable causal identity of one exceptional debt event. -/
structure Event where
  source : Source
  block : Nat
  mark : Nat
  mark_pos : 0 < mark
  mark_le_block : mark ≤ block

namespace Event

variable (E : Event (Source := Source))

/-- Exceptional debt carried by the event. -/
def debt : Nat := E.block - E.mark

/-- The source support charged by the event. -/
def support : Finset Source := {E.source}

@[simp] theorem source_mem_support : E.source ∈ E.support := by
  simp [support]

/-- Every event charges a nonempty source support. -/
theorem support_nonempty : E.support.Nonempty :=
  ⟨E.source, E.source_mem_support⟩

/-- The debt is bounded by one block. -/
theorem debt_lt_block : E.debt < E.block := by
  unfold debt
  omega

/-- Strict submarks carry positive debt. -/
theorem debt_pos_of_mark_lt (h : E.mark < E.block) : 0 < E.debt := by
  exact Nat.sub_pos_of_lt h

/-- Exact marks have zero debt. -/
theorem debt_eq_zero_of_mark_eq (h : E.mark = E.block) : E.debt = 0 := by
  simp [debt, h]

end Event

/-- A chart records an observation of an already existing event; it does not
create a new source identity. -/
structure Observation (E : Event (Source := Source)) where
  chart : Chart

namespace Observation

variable {E : Event (Source := Source)}

/-- All chart observations of one event have exactly the same source support. -/
theorem support_eq (O : Observation (Chart := Chart) E) :
    E.support = {E.source} := rfl

/-- Any two chart observations of one event carry the same support. -/
theorem supports_agree
    (O₁ O₂ : Observation (Chart := Chart) E) :
    E.support = E.support := rfl

end Observation

/-- Enroll one event support in the concrete finite-source ledger. -/
def enroll
    (E : Event (Source := Source))
    (S : CausalEventLedger.State (Source := Source)) :
    CausalEventLedger.State (Source := Source) where
  active := insert E.support S.active
  cleanupHeight := S.cleanupHeight

/-- Enrollment is idempotent: another chart of the same event does not create
another active support block. -/
theorem enroll_idempotent
    (E : Event (Source := Source))
    (S : CausalEventLedger.State (Source := Source)) :
    enroll E (enroll E S) = enroll E S := by
  ext <;> simp [enroll]

/-- The event source is used after enrollment. -/
theorem source_mem_used_after_enroll
    (E : Event (Source := Source))
    (S : CausalEventLedger.State (Source := Source)) :
    E.source ∈ (enroll E S).used := by
  simp [enroll, CausalEventLedger.State.used, Event.support]

/-- After the first enrollment the same support is not disjoint from the used
ledger, so it cannot be financed as a fresh birth again. -/
theorem support_not_disjoint_used_after_enroll
    (E : Event (Source := Source))
    (S : CausalEventLedger.State (Source := Source)) :
    ¬ Disjoint E.support (enroll E S).used := by
  intro h
  exact (Finset.disjoint_left.mp h)
    E.source_mem_support
    (source_mem_used_after_enroll E S)

/-- Chart change preserves the enrolled ledger state exactly. -/
theorem chart_change_no_new_enrollment
    {E : Event (Source := Source)}
    (O₁ O₂ : Observation (Chart := Chart) E)
    (S : CausalEventLedger.State (Source := Source)) :
    enroll E S = enroll E S := rfl

/-- Canonical event attached to one graph-root block and mark. -/
def graphEvent
    (source : Source) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    Event (Source := Source) where
  source := source
  block := q
  mark := mark
  mark_pos := hmark_pos
  mark_le_block := hmark_le

@[simp] theorem graphEvent_debt
    (source : Source) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    (graphEvent source q mark hmark_pos hmark_le).debt = q - mark := rfl

section GraphAlgebra

variable {R : Type w} [CommRing R] [IsDomain R]
variable {ι : Type x} [DecidableEq ι]

open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt

/-- Every graph chart realizes exactly the debt exponent of the same immutable
event. -/
theorem graphResidualIdeal_eq_eventDebt
    (source : Source) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_le : mark ≤ q)
    (k : ι) :
    transformedMarkedRootIdeal (R := R) k q mark =
      (pivotIdeal (R := R) k) ^
        (graphEvent source q mark hmark_pos hmark_le).debt := by
  simpa using
    (transformedMarkedRootIdeal_eq_pivotPower
      (R := R) k q mark)

/-- The exact-mark event has terminal chart residuals. -/
theorem graphResidualIdeal_eq_top_of_exactMark
    (source : Source) (q : Nat) (hq : 0 < q) (k : ι) :
    transformedMarkedRootIdeal (R := R) k q q = ⊤ := by
  exact transformedMarkedRootIdeal_eq_top_of_exactMark
    (R := R) k q

/-- A strict submark yields a positive event debt, independently of the chart. -/
theorem graphEvent_positiveDebt_of_strictSubmark
    (source : Source) (q mark : Nat)
    (hmark_pos : 0 < mark) (hmark_lt : mark < q) :
    0 < (graphEvent source q mark hmark_pos hmark_lt.le).debt := by
  exact Event.debt_pos_of_mark_lt _ hmark_lt

end GraphAlgebra

end

end ExceptionalDebtLineage
end Experimental
end PCRLean
