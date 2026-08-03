import Mathlib

/-!
# Finite exceptional-debt identity ledger

Fix a finite ancestor-source type and one Frobenius block `q > 0`.  A positive
mark in that block is represented by `Fin q`; the actual mark is `m+1` and the
exceptional debt exponent is

`q - (m+1)`.

Thus a debt identity is the pair `(source, mark)`.  It deliberately does not
contain a chart or pivot label.  Different standard charts are occurrences of
the same global event, not fresh births.

There are exactly `card(Source) * q` possible identities in one block.  Any
list of genuinely fresh debt identities therefore has bounded length.  This is
the finite-source/no-clone termination component for the pure exceptional debt
produced by arbitrary-mark Frobenius compression.  Changes of Frobenius block
remain controlled by the separate presentation-degree descent.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalDebtLedger

noncomputable section

universe u v

variable {Source : Type u} {Chart : Type v}

/-- One debt identity in a fixed Frobenius block. -/
abbrev DebtKey (Source : Type u) (q : Nat) := Source × Fin q

/-- The positive marked degree represented by the finite mark index. -/
def actualMark {q : Nat} (key : DebtKey Source q) : Nat :=
  key.2.val + 1

/-- Remaining pure exceptional exponent. -/
def exponent {q : Nat} (key : DebtKey Source q) : Nat :=
  q - actualMark key

/-- The represented mark lies in the block. -/
theorem actualMark_le_block {q : Nat} (key : DebtKey Source q) :
    actualMark key ≤ q := by
  exact key.2.isLt

/-- Every debt exponent is strictly below its nonzero Frobenius block. -/
theorem exponent_lt_block
    {q : Nat} (hq : 0 < q) (key : DebtKey Source q) :
    exponent key < q := by
  unfold exponent actualMark
  omega

/-- Exact mark has zero debt. -/
theorem exponent_eq_zero_of_actualMark_eq
    {q : Nat} (key : DebtKey Source q)
    (h : actualMark key = q) : exponent key = 0 := by
  simp [exponent, h]

/-- A strict submark has positive debt. -/
theorem exponent_pos_of_actualMark_lt
    {q : Nat} (key : DebtKey Source q)
    (h : actualMark key < q) : 0 < exponent key := by
  unfold exponent
  exact Nat.sub_pos_of_lt h

/-- One chart-local occurrence of a global debt identity. -/
structure Occurrence (Source : Type u) (Chart : Type v) (q : Nat) where
  key : DebtKey Source q
  chart : Chart

namespace Occurrence

/-- Transport changes only the chart label. -/
def transport {q : Nat}
    (o : Occurrence Source Chart q) (newChart : Chart) :
    Occurrence Source Chart q where
  key := o.key
  chart := newChart

@[simp] theorem transport_key {q : Nat}
    (o : Occurrence Source Chart q) (newChart : Chart) :
    (o.transport newChart).key = o.key := rfl

/-- Debt exponent is invariant under chart transport. -/
theorem exponent_transport {q : Nat}
    (o : Occurrence Source Chart q) (newChart : Chart) :
    exponent (o.transport newChart).key = exponent o.key := rfl

end Occurrence

section Finite

variable [Fintype Source] [DecidableEq Source]

/-- A finite ledger of already registered debt identities. -/
abbrev Ledger (Source : Type u) (q : Nat) := Finset (DebtKey Source q)

/-- Register one identity. -/
def register {q : Nat}
    (L : Ledger Source q) (key : DebtKey Source q) : Ledger Source q :=
  insert key L

/-- Registration never removes an old debt identity. -/
theorem subset_register {q : Nat}
    (L : Ledger Source q) (key : DebtKey Source q) :
    L ⊆ register L key := by
  intro x hx
  exact Finset.mem_insert_of_mem hx

/-- A genuinely fresh registration increases ledger cardinality exactly once. -/
theorem card_register_of_fresh {q : Nat}
    (L : Ledger Source q) (key : DebtKey Source q)
    (hfresh : key ∉ L) :
    (register L key).card = L.card + 1 := by
  simp [register, hfresh]

/-- Number of possible debt identities in one fixed block. -/
theorem card_debtKey (q : Nat) :
    Fintype.card (DebtKey Source q) = Fintype.card Source * q := by
  simp [DebtKey]

/-- Every ledger is bounded by the finite source/mark capacity. -/
theorem ledger_card_le_capacity {q : Nat} (L : Ledger Source q) :
    L.card ≤ Fintype.card Source * q := by
  calc
    L.card ≤ Fintype.card (DebtKey Source q) := Finset.card_le_univ L
    _ = Fintype.card Source * q := card_debtKey q

/-- A genuinely fresh history in one block has bounded length. -/
theorem fresh_history_length_le_capacity {q : Nat}
    (history : List (DebtKey Source q))
    (hfresh : history.Nodup) :
    history.length ≤ Fintype.card Source * q := by
  calc
    history.length ≤ Fintype.card (DebtKey Source q) :=
      List.Nodup.length_le_card hfresh
    _ = Fintype.card Source * q := card_debtKey q

end Finite

end

end ExceptionalDebtLedger
end Experimental
end PCRLean
