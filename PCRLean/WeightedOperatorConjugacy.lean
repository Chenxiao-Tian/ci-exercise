import Mathlib
import PCRLean.WeightedOperatorLedger

/-!
# Presentation transport for weighted operator packets

A finite weighted differential packet must not depend on a chosen ring
presentation.  This file isolates the exact transport statement.  Two weighted
operator families are conjugate when a ring equivalence intertwines their
additive operators and preserves every operator cost.

Conjugacy transports all finite words, total costs, and the finite packet
visible below any fixed mark.  Hence coordinate changes cannot create, delete,
or recharge a weighted descendant merely by changing presentation.
-/

namespace PCRLean
namespace WeightedOperatorConjugacy

noncomputable section

universe u v w

variable {R : Type u} {S : Type v} {κ : Type w}
variable [CommRing R] [CommRing S]

/-- Cost-preserving conjugacy of two weighted operator families. -/
structure Conjugacy
    (e : R ≃+* S)
    (opsR : κ → WeightedOperatorLedger.Operator (R := R))
    (opsS : κ → WeightedOperatorLedger.Operator (R := S)) : Prop where
  cost_eq : ∀ i, (opsR i).cost = (opsS i).cost
  op_eq : ∀ i x, e ((opsR i).op x) = (opsS i).op (e x)

namespace Conjugacy

variable {e : R ≃+* S}
variable {opsR : κ → WeightedOperatorLedger.Operator (R := R)}
variable {opsS : κ → WeightedOperatorLedger.Operator (R := S)}
variable (C : Conjugacy e opsR opsS)

/-- Total marked cost is presentation independent. -/
theorem wordCost_eq (word : List κ) :
    WeightedOperatorLedger.wordCost opsR word =
      WeightedOperatorLedger.wordCost opsS word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp only [WeightedOperatorLedger.wordCost_cons]
      rw [C.cost_eq i, ih]

/-- Every finite operator word is transported by the conjugacy. -/
theorem applyWord_eq (word : List κ) (x : R) :
    e (WeightedOperatorLedger.applyWord opsR word x) =
      WeightedOperatorLedger.applyWord opsS word (e x) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp only [WeightedOperatorLedger.applyWord_cons]
      rw [C.op_eq i, ih]

/-- The complete weighted descendant pair is transported exactly. -/
theorem descendantPair_eq (word : List κ) (x : R) (b : Nat) :
    (e (WeightedOperatorLedger.applyWord opsR word x),
      b - WeightedOperatorLedger.wordCost opsR word) =
    (WeightedOperatorLedger.applyWord opsS word (e x),
      b - WeightedOperatorLedger.wordCost opsS word) := by
  rw [C.applyWord_eq word x, C.wordCost_eq word]

section FiniteAlphabet

variable [Fintype κ] [DecidableEq κ]

/-- Membership in the finite packet visible below a fixed mark transports
forward through a conjugacy. -/
theorem map_mem_descendantPacket
    (seed : R) (b : Nat) {entry : R × Nat}
    (hentry : entry ∈
      WeightedOperatorLedger.descendantPacket opsR seed b) :
    (e entry.1, entry.2) ∈
      WeightedOperatorLedger.descendantPacket opsS (e seed) b := by
  rcases WeightedOperatorLedger.descendantPacket_sound
      opsR seed b hentry with ⟨word, hcost, hentryEq⟩
  subst entry
  have hcostS : WeightedOperatorLedger.wordCost opsS word ≤ b := by
    simpa [C.wordCost_eq word] using hcost
  have hmem := WeightedOperatorLedger.mem_descendantPacket_of_cost_le
    opsS (e seed) b word hcostS
  simpa [C.applyWord_eq word seed, C.wordCost_eq word] using hmem

/-- Packet membership is equivalent in the two presentations. -/
theorem mem_descendantPacket_iff
    (seed : R) (b : Nat) (entry : R × Nat) :
    entry ∈ WeightedOperatorLedger.descendantPacket opsR seed b ↔
      (e entry.1, entry.2) ∈
        WeightedOperatorLedger.descendantPacket opsS (e seed) b := by
  constructor
  · exact C.map_mem_descendantPacket seed b
  · intro h
    let Csymm : Conjugacy e.symm opsS opsR where
      cost_eq := fun i => (C.cost_eq i).symm
      op_eq := by
        intro i y
        apply e.injective
        simpa using (C.op_eq i (e.symm y)).symm
    have hback := Csymm.map_mem_descendantPacket (e seed) b h
    simpa using hback

end FiniteAlphabet

end Conjugacy

end

end WeightedOperatorConjugacy
end PCRLean
