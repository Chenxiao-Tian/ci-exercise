import Mathlib
import PCRLean.FiniteWeightedMarkedClosure
import PCRLean.WeightedOperatorConjugacy

/-!
# Presentation invariance of finite weighted marked closure

A cost-preserving conjugacy of weighted operator families transports not only
individual descendants but the actual image ideals and every residual level of
the finite marked closure.  Thus the finite packet constructed from a marked
ideal is independent of a chosen ring presentation whenever the intrinsic
operators are related by conjugacy.

This is the local algebraic presentation-independence theorem required by the
universal packetization layer.
-/

namespace PCRLean
namespace FiniteWeightedClosureConjugacy

noncomputable section

universe u v w

variable {R : Type u} {S : Type v} {κ : Type w}
variable [CommRing R] [CommRing S]
variable [Fintype κ] [DecidableEq κ]

variable {e : R ≃+* S}
variable {opsR : κ → WeightedOperatorLedger.Operator (R := R)}
variable {opsS : κ → WeightedOperatorLedger.Operator (R := S)}

/-- Mapping an operator-word image ideal through a conjugacy gives the
corresponding word-image ideal in the new presentation. -/
theorem map_wordImageIdeal_eq
    (C : WeightedOperatorConjugacy.Conjugacy e opsR opsS)
    (I : Ideal R) (word : List κ) :
    (FiniteWeightedMarkedClosure.wordImageIdeal opsR I word).map
        e.toRingHom =
      FiniteWeightedMarkedClosure.wordImageIdeal
        opsS (I.map e.toRingHom) word := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap,
      FiniteWeightedMarkedClosure.wordImageIdeal, Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    change e (WeightedOperatorLedger.applyWord opsR word x) ∈
      FiniteWeightedMarkedClosure.wordImageIdeal
        opsS (I.map e.toRingHom) word
    rw [C.applyWord_eq word x]
    apply Ideal.subset_span
    exact ⟨e x, Ideal.mem_map_of_mem e.toRingHom hx, rfl⟩
  · rw [FiniteWeightedMarkedClosure.wordImageIdeal, Ideal.span_le]
    rintro y ⟨z, hz, rfl⟩
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hz
    rcases hz with ⟨x, hx, rfl⟩
    rw [← C.applyWord_eq word x]
    exact Ideal.mem_map_of_mem e.toRingHom
      (Ideal.subset_span ⟨x, hx, rfl⟩)

/-- Residual-word membership is presentation independent. -/
theorem mem_wordsAtResidual_iff
    (C : WeightedOperatorConjugacy.Conjugacy e opsR opsS)
    (b m : Nat) (word : List κ) :
    word ∈ FiniteWeightedMarkedClosure.wordsAtResidual opsR b m ↔
      word ∈ FiniteWeightedMarkedClosure.wordsAtResidual opsS b m := by
  simp only [FiniteWeightedMarkedClosure.mem_wordsAtResidual_iff]
  rw [C.wordCost_eq word]

/-- One inclusion in transport of a complete residual level. -/
theorem map_levelIdeal_le
    (C : WeightedOperatorConjugacy.Conjugacy e opsR opsS)
    (I : Ideal R) (b m : Nat) :
    (FiniteWeightedMarkedClosure.levelIdeal opsR I b m).map
        e.toRingHom ≤
      FiniteWeightedMarkedClosure.levelIdeal
        opsS (I.map e.toRingHom) b m := by
  rw [Ideal.map_le_iff_le_comap,
    FiniteWeightedMarkedClosure.levelIdeal]
  apply Finset.sup_le
  intro word hword
  rw [← Ideal.map_le_iff_le_comap]
  rw [map_wordImageIdeal_eq C I word]
  apply Finset.le_sup
  exact (mem_wordsAtResidual_iff C b m word).1 hword

/-- Canonical symmetric conjugacy. -/
def symmConjugacy
    (C : WeightedOperatorConjugacy.Conjugacy e opsR opsS) :
    WeightedOperatorConjugacy.Conjugacy e.symm opsS opsR where
  cost_eq := fun i => (C.cost_eq i).symm
  op_eq := by
    intro i y
    apply e.injective
    simpa using (C.op_eq i (e.symm y)).symm

/-- Mapping an ideal through a ring equivalence and back recovers it. -/
theorem map_symm_map (I : Ideal R) :
    (I.map e.toRingHom).map e.symm.toRingHom = I := by
  rw [Ideal.map_map]
  convert Ideal.map_id I using 1
  ext x
  simp

/-- Every residual level of the finite weighted closure is transported exactly
under a cost-preserving operator conjugacy. -/
theorem map_levelIdeal_eq
    (C : WeightedOperatorConjugacy.Conjugacy e opsR opsS)
    (I : Ideal R) (b m : Nat) :
    (FiniteWeightedMarkedClosure.levelIdeal opsR I b m).map
        e.toRingHom =
      FiniteWeightedMarkedClosure.levelIdeal
        opsS (I.map e.toRingHom) b m := by
  apply le_antisymm
  · exact map_levelIdeal_le C I b m
  · intro y hy
    have hback := map_levelIdeal_le (symmConjugacy C)
      (I.map e.toRingHom) b m
    have hyback : e.symm y ∈
        (FiniteWeightedMarkedClosure.levelIdeal
          opsS (I.map e.toRingHom) b m).map e.symm.toRingHom :=
      Ideal.mem_map_of_mem e.symm.toRingHom hy
    have hmem := hback hyback
    have hsource : e.symm y ∈
        FiniteWeightedMarkedClosure.levelIdeal opsR I b m := by
      simpa [map_symm_map (e := e) I] using hmem
    simpa using Ideal.mem_map_of_mem e.toRingHom hsource

end

end FiniteWeightedClosureConjugacy
end PCRLean
