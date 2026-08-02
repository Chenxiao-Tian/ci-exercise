import Mathlib
import PCRLean.MarkedIdeal

namespace PCRLean
namespace OwnerJoint

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- The finite union ideal of active owners with a common mark. -/
def activeUnion (owners : ι → Ideal R) (s : Finset ι) : Ideal R :=
  s.sup owners

/-- If every active owner is contained in one marked centre power, their
finite union is contained in the same power. -/
theorem activeUnion_le_centre_pow
    (owners : ι → Ideal R) (s : Finset ι) (C : Ideal R) (m : Nat)
    (h : ∀ i ∈ s, owners i ≤ C ^ m) :
    activeUnion owners s ≤ C ^ m := by
  classical
  rw [activeUnion]
  exact Finset.sup_le h

/-- The corresponding aggregate marked packet is permissible. -/
theorem aggregate_permissible
    (owners : ι → Ideal R) (s : Finset ι) (C : Ideal R) (m : Nat)
    (hm : 0 < m) (h : ∀ i ∈ s, owners i ≤ C ^ m) :
    MarkedIdeal.Permissible
      (R := R) ⟨activeUnion owners s, m, hm⟩ C :=
  activeUnion_le_centre_pow owners s C m h

/-- Adding a newly certified active owner preserves joint permissibility. -/
theorem insert_owner_preserves
    [DecidableEq ι] (owners : ι → Ideal R) (s : Finset ι)
    (i : ι) (C : Ideal R) (m : Nat)
    (hi : owners i ≤ C ^ m)
    (hs : activeUnion owners s ≤ C ^ m) :
    activeUnion owners (insert i s) ≤ C ^ m := by
  apply activeUnion_le_centre_pow
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hi
  · exact (Finset.le_sup (f := owners) hb).trans hs

/-- Removing an owner cannot destroy joint permissibility. -/
theorem subset_preserves
    (owners : ι → Ideal R) {s t : Finset ι} (hst : s ⊆ t)
    {C : Ideal R} {m : Nat}
    (ht : activeUnion owners t ≤ C ^ m) :
    activeUnion owners s ≤ C ^ m := by
  classical
  apply le_trans ?_ ht
  rw [activeUnion, activeUnion]
  exact Finset.sup_mono hst

/-- Active divisibility alone says nothing about an unrelated passive
predicate. This logical separation prevents silent inference of passive
normal-flatness from marked containment. -/
theorem active_does_not_imply_arbitrary_passive
    (active : Prop) (passive : Prop) (ha : active) (hnp : ¬ passive) :
    ¬ (active → passive) := by
  intro h
  exact hnp (h ha)

end OwnerJoint
end PCRLean
