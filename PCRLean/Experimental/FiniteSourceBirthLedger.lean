import Mathlib
import PCRLean.GenerationalRank

/-!
# Experimental finite-source birth ledger

A genuinely independent geometric birth must consume a nonempty set of
previously unused atoms from one fixed finite ancestor-source set.  The ledger
records the cumulative used atoms.  Registering a fresh disjoint support
strictly increases the used-cardinality and therefore strictly decreases the
number of unused atoms.

This proves that independent births satisfying no-clone and no-recharge cannot
occur infinitely often.  It does not construct the ancestor support of an
arbitrary geometric birth, prove hereditary support transport through blowup
charts, or classify dependent births by a separate local rank.
-/

namespace PCRLean
namespace Experimental
namespace FiniteSourceBirthLedger

noncomputable section

universe u

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- Cumulative set of ancestor atoms already charged to genuine births. -/
structure Ledger where
  used : Finset Source
  deriving Repr, DecidableEq

/-- Number of ancestor atoms still available for future independent births. -/
def unusedCount (L : Ledger (Source := Source)) : Nat :=
  Fintype.card Source - L.used.card

/-- One legal independent birth: add a nonempty support disjoint from every
previously charged source atom. -/
def Step (parent child : Ledger (Source := Source)) : Prop :=
  ∃ newborn : Finset Source,
    newborn.Nonempty ∧
    Disjoint parent.used newborn ∧
    child.used = parent.used ∪ newborn

/-- Every ledger uses at most the total number of ancestor atoms. -/
theorem used_card_le_total (L : Ledger (Source := Source)) :
    L.used.card ≤ Fintype.card Source := by
  have hcard : L.used.card ≤ (Finset.univ : Finset Source).card :=
    Finset.card_le_card (Finset.subset_univ L.used)
  simpa using hcard

/-- Registering one legal birth strictly increases cumulative used support. -/
theorem used_card_strictly_increases
    {parent child : Ledger (Source := Source)}
    (h : Step parent child) :
    parent.used.card < child.used.card := by
  rcases h with ⟨newborn, hnew, hdisj, hchild⟩
  rw [hchild, Finset.card_union_of_disjoint hdisj]
  have hpos : 0 < newborn.card := Finset.card_pos.mpr hnew
  omega

/-- Equivalently, every independent birth strictly lowers the unused-source
rank. -/
theorem unusedCount_strictly_decreases
    {parent child : Ledger (Source := Source)}
    (h : Step parent child) :
    unusedCount child < unusedCount parent := by
  have hparent := used_card_le_total parent
  have hchild := used_card_le_total child
  have hstrict := used_card_strictly_increases h
  simp only [unusedCount]
  omega

/-- Once all ancestor atoms are charged, no new disjoint nonempty birth can be
registered. -/
theorem no_step_from_full
    {parent child : Ledger (Source := Source)}
    (hfull : parent.used = Finset.univ) :
    ¬ Step parent child := by
  rintro ⟨newborn, hnew, hdisj, hchild⟩
  rcases hnew with ⟨s, hsnew⟩
  have hsparent : s ∈ parent.used := by
    rw [hfull]
    simp
  exact (Finset.disjoint_left.mp hdisj) hsparent hsnew

/-- There is no infinite path of genuinely independent births over a fixed
finite ancestor-source set. -/
theorem no_infinite_birth_path :
    ¬ ∃ f : Nat → Ledger (Source := Source),
      ∀ n, Step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending Nat.lt_wfRel.wf
    (fun n => unusedCount (f n))
    (fun n => unusedCount_strictly_decreases (hf n))

end

end FiniteSourceBirthLedger
end Experimental
end PCRLean
