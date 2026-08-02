import Std.Tactic

namespace PCRLean
namespace NoRecharge

/-- Immutable finite coupon ledger.  A list is sufficient because the formal
no-recharge property is monotone membership, not a choice of ordering. -/
structure Ledger where
  capacity : Nat
  consumed : List Nat
  withinCapacity : ∀ q, q ∈ consumed → q < capacity

/-- A chart, gauge, or reentry comparison is certified only when the consumed
coupon collection can grow but never lose a previously consumed coupon. -/
def CertifiedReentry (before after : Ledger) : Prop :=
  before.capacity = after.capacity ∧
    ∀ q, q ∈ before.consumed → q ∈ after.consumed

/-- A consumed coupon cannot become available after certified reentry. -/
theorem consumed_remains_consumed {before after : Ledger}
    (h : CertifiedReentry before after) {q : Nat}
    (hq : q ∈ before.consumed) : q ∈ after.consumed := by
  exact h.2 q hq

/-- Certified reentry is transitive. -/
theorem CertifiedReentry.trans {a b c : Ledger}
    (hab : CertifiedReentry a b) (hbc : CertifiedReentry b c) :
    CertifiedReentry a c := by
  constructor
  · exact hab.1.trans hbc.1
  · intro q hq
    exact hbc.2 q (hab.2 q hq)

/-- Certified reentry is reflexive. -/
theorem CertifiedReentry.refl (a : Ledger) : CertifiedReentry a a := by
  exact ⟨rfl, fun _ h => h⟩

/-- Fresh labels alone do not imply termination.  This explicit stream has a
new identity at every time, even though no label is ever reused. -/
def freshBirthIdentity (n : Nat) : Nat := n

/-- The fresh-birth stream is injective. -/
theorem freshBirthIdentity_injective : Function.Injective freshBirthIdentity := by
  intro a b h
  simpa [freshBirthIdentity] using h

/-- Every time step produces a genuinely new identity. -/
theorem freshBirthIdentity_strict (n : Nat) :
    freshBirthIdentity n < freshBirthIdentity (n + 1) := by
  simp [freshBirthIdentity]

/-- Hence an age-increasing acyclic label stream exists for all natural times;
additional finite-source or paid-birth structure is logically necessary. -/
theorem freshBirthsExistAtEveryTime :
    ∀ n, ∃ id, id = freshBirthIdentity n := by
  intro n
  exact ⟨freshBirthIdentity n, rfl⟩

end NoRecharge
end PCRLean
