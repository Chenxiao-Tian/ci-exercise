import Mathlib
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Dershowitz-Manna packet-multiset termination

A finite family of active packets is globally smaller when one or more old
packets are removed and replaced by finitely many packets, each of which is
strictly smaller than one of the removed packets.  This is the formal
termination backend frozen in the PCR escape-tree architecture; it combines
local strict geometric replacement theorems but does not create them.
-/

namespace PCRLean.Termination.PacketMultiset

variable {α : Type*} [Preorder α] [WellFoundedLT α]

/-- The standard Dershowitz-Manna order on finite packet multisets. -/
abbrev PacketLt : Multiset α → Multiset α → Prop :=
  Multiset.IsDershowitzMannaLT

/-- The packet multiset order is well founded whenever the underlying packet
rank is well founded. -/
theorem packetLt_wellFounded : WellFounded (PacketLt : Multiset α → Multiset α → Prop) :=
  Multiset.wellFounded_isDershowitzMannaLT

/-- Replacing a nonempty block `Z` by a block `Y`, every element of which is
strictly below some removed element, strictly lowers the packet multiset. -/
theorem replace_block_lt (X Y Z : Multiset α) (hZ : Z ≠ 0)
    (hYZ : ∀ y, y ∈ Y → ∃ z, z ∈ Z ∧ y < z) :
    PacketLt (X + Y) (X + Z) := by
  exact ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩

/-- The common one-parent replacement rule. -/
theorem replace_one_lt (X Y : Multiset α) (z : α)
    (hY : ∀ y, y ∈ Y → y < z) :
    PacketLt (X + Y) (X + {z}) := by
  apply replace_block_lt X Y {z}
  · simp
  · intro y hy
    exact ⟨z, by simp, hY y hy⟩

/-- Deleting one active packet is a strict multiset decrease. -/
theorem erase_one_lt (X : Multiset α) (z : α) :
    PacketLt X (X + {z}) := by
  simpa using (replace_one_lt (α := α) X 0 z (by simp))

/-- A transition system ranked by a finite multiset of well-founded packet
ranks. -/
structure PacketSystem where
  State : Type*
  step : State → State → Prop
  packets : State → Multiset α
  step_decreases : ∀ {child parent}, step child parent →
    PacketLt (packets child) (packets parent)

namespace PacketSystem

variable (S : PacketSystem (α := α))

/-- Every packet-ranked transition system is well founded. -/
theorem step_wellFounded : WellFounded S.step := by
  have hPacket : WellFounded (PacketLt : Multiset α → Multiset α → Prop) :=
    packetLt_wellFounded
  exact (hPacket.onFun (f := S.packets)).mono
    (fun _ _ hstep => S.step_decreases hstep)

/-- Hence no infinite certified packet-replacement chain exists. -/
theorem no_infinite_chain :
    IsEmpty {f : ℕ → S.State // ∀ n, S.step (f (n + 1)) (f n)} :=
  wellFounded_iff_isEmpty_descending_chain.mp S.step_wellFounded

end PacketSystem

end PCRLean.Termination.PacketMultiset
