import Mathlib
import PCRLean.Algebra.MarkedIdeal

/-!
# Finite joint-owner permissibility

A centre is jointly permissible only when the same actual ideal satisfies every
active marked owner.  This file packages the finite conjunction and proves
that owners with a common mark can be combined by the supremum of their ideals.
It is an acceptance theorem, not an existence theorem for a common centre and
not a passive normal-flatness theorem.
-/

namespace PCRLean.Algebra.JointOwners

variable {R : Type*} [CommRing R]

/-- The supremum of a finite list of ideals. -/
def combinedIdeal : List (Ideal R) → Ideal R
  | [] => ⊥
  | I :: Is => I ⊔ combinedIdeal Is

@[simp] theorem combinedIdeal_nil : combinedIdeal ([] : List (Ideal R)) = ⊥ := rfl

@[simp] theorem combinedIdeal_cons (I : Ideal R) (Is : List (Ideal R)) :
    combinedIdeal (I :: Is) = I ⊔ combinedIdeal Is := rfl

/-- A finite family of marked owners is jointly permissible for one centre. -/
def JointlyPermissible (owners : List (PCRLean.Algebra.MarkedIdeal R))
    (C : Ideal R) : Prop :=
  ∀ M ∈ owners, M.Permissible C

@[simp] theorem jointlyPermissible_nil (C : Ideal R) :
    JointlyPermissible [] C := by
  intro M hM
  simp at hM

@[simp] theorem jointlyPermissible_cons
    (M : PCRLean.Algebra.MarkedIdeal R)
    (owners : List (PCRLean.Algebra.MarkedIdeal R)) (C : Ideal R) :
    JointlyPermissible (M :: owners) C ↔
      M.Permissible C ∧ JointlyPermissible owners C := by
  constructor
  · intro h
    constructor
    · exact h M (by simp)
    · intro N hN
      exact h N (by simp [hN])
  · rintro ⟨hM, hrest⟩ N hN
    rcases List.mem_cons.mp hN with rfl | hN
    · exact hM
    · exact hrest N hN

/-- The combined ideal is below `J` exactly when every listed ideal is below
`J`. -/
theorem combinedIdeal_le_iff (Is : List (Ideal R)) (J : Ideal R) :
    combinedIdeal Is ≤ J ↔ ∀ I ∈ Is, I ≤ J := by
  induction Is with
  | nil => simp
  | cons I Is ih =>
      simp [combinedIdeal, sup_le_iff, ih]

/-- Common-mark owners that are individually permissible can be represented by
one combined owner ideal without weakening the centre condition. -/
theorem combined_owner_permissible {b : ℕ} (hb : 0 < b)
    (Is : List (Ideal R)) (C : Ideal R)
    (h : ∀ I ∈ Is, I ≤ C ^ b) :
    (PCRLean.Algebra.MarkedIdeal.mk (combinedIdeal Is) b hb).Permissible C := by
  exact (combinedIdeal_le_iff Is (C ^ b)).2 h

/-- Conversely, permissibility of the combined common-mark owner implies
permissibility of every constituent owner. -/
theorem each_owner_permissible_of_combined {b : ℕ} (hb : 0 < b)
    (Is : List (Ideal R)) (C : Ideal R)
    (h : (PCRLean.Algebra.MarkedIdeal.mk (combinedIdeal Is) b hb).Permissible C) :
    ∀ I ∈ Is, I ≤ C ^ b :=
  (combinedIdeal_le_iff Is (C ^ b)).1 h

end PCRLean.Algebra.JointOwners
