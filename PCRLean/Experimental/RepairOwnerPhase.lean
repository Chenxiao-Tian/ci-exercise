import Mathlib

/-!
# One-way repair-owner enrollment semantics

A module whose strict transform is intentionally being changed by a
flatification or Cartier-trace word is a repair owner, not an already passive
owner.  Once the target flatness certificate is obtained it may be enrolled as
passive; a zero defect may be discharged.  Neither a passive nor a discharged
owner may silently return to repair status.

This file records the exact finite-state semantics.  It does not construct any
flatness, Tor, strict-transform, or resolution certificate.
-/

namespace PCRLean
namespace Experimental
namespace RepairOwnerPhase

/-- Owner mode relevant to the repair/passive distinction. -/
inductive Phase where
  | repair
  | passive
  | discharged
  deriving DecidableEq, Repr

/-- Legal one-owner phase transitions.  A repair step may consume debt while
remaining in repair mode, enroll the owner as passive, or discharge a zero
owner.  Terminal modes are preserved. -/
inductive LegalTransition : Phase → Phase → Prop where
  | repairStep : LegalTransition .repair .repair
  | enroll : LegalTransition .repair .passive
  | discharge : LegalTransition .repair .discharged
  | preservePassive : LegalTransition .passive .passive
  | preserveDischarged : LegalTransition .discharged .discharged

/-- Boolean/numerical unresolved-repair coordinate. -/
def repairWeight : Phase → ℕ
  | .repair => 1
  | .passive => 0
  | .discharged => 0

/-- Enrollment strictly lowers the repair coordinate. -/
@[simp] theorem enroll_weight_drop :
    repairWeight .passive < repairWeight .repair := by
  decide

/-- Zero discharge strictly lowers the repair coordinate. -/
@[simp] theorem discharge_weight_drop :
    repairWeight .discharged < repairWeight .repair := by
  decide

/-- Legal transitions can never reset an enrolled passive owner to repair. -/
theorem no_passive_reset :
    ¬ LegalTransition .passive .repair := by
  intro h
  cases h

/-- Legal transitions can never resurrect a discharged owner. -/
theorem no_discharged_reset :
    ¬ LegalTransition .discharged .repair := by
  intro h
  cases h

/-- Every legal transition weakly decreases the unresolved-repair coordinate. -/
theorem weight_antitone
    {oldPhase newPhase : Phase}
    (h : LegalTransition oldPhase newPhase) :
    repairWeight newPhase ≤ repairWeight oldPhase := by
  cases h <;> decide

/-- A legal transition has equal repair weight only in a phase-preserving
step. -/
theorem weight_eq_cases
    {oldPhase newPhase : Phase}
    (h : LegalTransition oldPhase newPhase)
    (hw : repairWeight newPhase = repairWeight oldPhase) :
    oldPhase = newPhase := by
  cases h <;> simp [repairWeight] at hw ⊢

/-- Every strict mode change from repair is either enrollment or discharge. -/
theorem repair_exit_classification
    {newPhase : Phase}
    (h : LegalTransition .repair newPhase)
    (hne : newPhase ≠ .repair) :
    newPhase = .passive ∨ newPhase = .discharged := by
  cases h
  · exact (hne rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

end RepairOwnerPhase
end Experimental
end PCRLean
