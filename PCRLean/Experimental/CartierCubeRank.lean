import Mathlib

/-!
# Finite Cartier-cube depth rank

For an SNC exceptional family indexed by a finite type, a Cartier stratum is
labelled by the set of components already imposed.  Passing to one additional
missing component strictly lowers the number of remaining components.  This is
the finite combinatorial rank behind the iterated Cartier local criterion.

The file proves only depth arithmetic and exact terminal detection.  It does
not prove the module-theoretic Cartier flatness criterion or construct any
geometric special-fibre legalization.
-/

namespace PCRLean
namespace Experimental
namespace CartierCubeRank

noncomputable section

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Number of Cartier components not yet imposed on the current stratum. -/
def rank (S : Finset α) : ℕ :=
  Fintype.card α - S.card

/-- A stratum whose label set is the whole boundary family has rank zero. -/
@[simp] theorem rank_univ : rank (Finset.univ : Finset α) = 0 := by
  simp [rank]

/-- Rank zero detects the deepest stratum, provided the label set is a subset
of the finite boundary family (automatically true for a `Finset α`). -/
theorem rank_eq_zero_iff (S : Finset α) :
    rank S = 0 ↔ S = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    have hcard : (insert i S).card ≤ Fintype.card α := by
      simpa using Finset.card_le_card
        (show insert i S ⊆ (Finset.univ : Finset α) by simp)
    have hins : (insert i S).card = S.card + 1 :=
      Finset.card_insert_of_not_mem hi
    have hS : Fintype.card α ≤ S.card := by
      simpa [rank, Nat.sub_eq_zero_iff_le] using h
    omega
  · rintro rfl
    exact rank_univ

/-- Inserting one genuinely missing Cartier component strictly lowers the cube
rank. -/
theorem insert_missing_drop
    (S : Finset α) {i : α} (hi : i ∉ S) :
    rank (insert i S) < rank S := by
  have hcard : (insert i S).card ≤ Fintype.card α := by
    simpa using Finset.card_le_card
      (show insert i S ⊆ (Finset.univ : Finset α) by simp)
  rw [rank, rank, Finset.card_insert_of_not_mem hi]
  omega

/-- Every nonterminal Cartier stratum has a missing component.  The theorem
returns existence only; the geometric algorithm retains the full finite set of
missing components rather than selecting one canonically. -/
theorem exists_missing_of_ne_univ
    {S : Finset α} (hS : S ≠ Finset.univ) :
    ∃ i : α, i ∉ S := by
  by_contra h
  push_neg at h
  exact hS (Finset.eq_univ_iff_forall.mpr h)

/-- The natural-number cube-depth order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : ℕ → ℕ → Prop) :=
  Nat.lt_wfRel.wf

end

end CartierCubeRank
end Experimental
end PCRLean
