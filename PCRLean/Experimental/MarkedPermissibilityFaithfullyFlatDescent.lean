import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.MarkedIdeal

/-!
# Faithfully flat descent of marked permissibility and centre gates

Let `A → B` be faithfully flat.  Marked-power containment is fpqc local in the
following exact sense:

`I B ≤ (C B)^m  ↔  I ≤ C^m`.

The forward implication contracts membership using
`(J B) ∩ A = J`; the reverse implication is ordinary ideal extension.  Thus
active-owner permissibility can be checked on a faithfully flat graph or
coordinate atlas without weakening the marked power.

The same argument shows that extension reflects equality of ideals and hence
reflects both forbidden centre degeneracies:

* `C = ⊤`, the empty closed centre; and
* `C = ⊥`, the whole ambient space.

This module does not descend regularity, finite presentation, passive Tor
safety, boundary SNC, or blowup-chart data.  Those remain independent gates.
-/

namespace PCRLean
namespace Experimental
namespace MarkedPermissibilityFaithfullyFlatDescent

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Extension of an ideal along the faithfully flat algebra map. -/
def extend (I : Ideal A) : Ideal B :=
  Ideal.map (algebraMap A B) I

/-- Ideal extension commutes with powers. -/
theorem extend_pow (I : Ideal A) (m : Nat) :
    extend (B := B) (I ^ m) = (extend (B := B) I) ^ m := by
  exact Ideal.map_pow (algebraMap A B) I m

/-- Membership in an ideal is reflected by faithfully flat extension. -/
theorem mem_iff_map_mem_extend (I : Ideal A) (x : A) :
    x ∈ I ↔ algebraMap A B x ∈ extend (B := B) I := by
  change x ∈ I ↔ x ∈ (extend (B := B) I).comap (algebraMap A B)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- Inclusion of extended ideals descends. -/
theorem le_of_extend_le
    {I J : Ideal A}
    (h : extend (B := B) I ≤ extend (B := B) J) :
    I ≤ J := by
  intro x hx
  have hxB : algebraMap A B x ∈ extend (B := B) I :=
    Ideal.mem_map_of_mem (algebraMap A B) hx
  exact (mem_iff_map_mem_extend (B := B) J x).mpr (h hxB)

/-- Faithfully flat extension reflects equality of ideals. -/
theorem extend_eq_iff {I J : Ideal A} :
    extend (B := B) I = extend (B := B) J ↔ I = J := by
  constructor
  · intro h
    apply le_antisymm
    · exact le_of_extend_le (B := B) h.le
    · exact le_of_extend_le (B := B) h.ge
  · intro h
    simpa [h]

/-- Extension reflects the empty closed centre `⊤`. -/
theorem extend_eq_top_iff (I : Ideal A) :
    extend (B := B) I = ⊤ ↔ I = ⊤ := by
  rw [← show extend (B := B) (⊤ : Ideal A) = ⊤ by simp [extend],
    extend_eq_iff (B := B)]

/-- Extension reflects the whole ambient centre `⊥`. -/
theorem extend_eq_bot_iff (I : Ideal A) :
    extend (B := B) I = ⊥ ↔ I = ⊥ := by
  rw [← show extend (B := B) (⊥ : Ideal A) = ⊥ by simp [extend],
    extend_eq_iff (B := B)]

/-- Marked containment ascends along any algebra map. -/
theorem extend_le_pow_of_le_pow
    {I C : Ideal A} {m : Nat}
    (h : I ≤ C ^ m) :
    extend (B := B) I ≤ (extend (B := B) C) ^ m := by
  rw [← extend_pow (B := B)]
  exact Ideal.map_mono h

/-- Marked containment descends along a faithfully flat algebra map. -/
theorem le_pow_of_extend_le_pow
    {I C : Ideal A} {m : Nat}
    (h : extend (B := B) I ≤ (extend (B := B) C) ^ m) :
    I ≤ C ^ m := by
  rw [← extend_pow (B := B)] at h
  exact le_of_extend_le (B := B) h

/-- Exact fpqc locality of marked-power containment. -/
theorem extend_le_pow_iff
    {I C : Ideal A} {m : Nat} :
    extend (B := B) I ≤ (extend (B := B) C) ^ m ↔
      I ≤ C ^ m := by
  exact ⟨le_pow_of_extend_le_pow (B := B),
    extend_le_pow_of_le_pow (B := B)⟩

/-- Extension of a marked packet, preserving its mark exactly. -/
def extendPacket (P : MarkedIdeal.Packet A) : MarkedIdeal.Packet B where
  ideal := extend (B := B) P.ideal
  mark := P.mark
  mark_pos := P.mark_pos

/-- Marked permissibility is faithfully flat local. -/
theorem permissible_extend_iff
    (P : MarkedIdeal.Packet A) (C : Ideal A) :
    MarkedIdeal.Permissible (extendPacket (B := B) P)
        (extend (B := B) C) ↔
      MarkedIdeal.Permissible P C := by
  exact extend_le_pow_iff (B := B)

end

end MarkedPermissibilityFaithfullyFlatDescent
end Experimental
end PCRLean
