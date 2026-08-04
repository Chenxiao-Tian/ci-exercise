import Mathlib
import PCRLean.Experimental.CanonicalMarkedMinimizerSpace

/-!
# A two-choice symmetry obstruction to canonical minimal closure

For the acceptance predicate "the selected finite family is nonempty" on a
Boolean two-element component set, the two singleton families are exactly the
cardinal-minimal acceptable families.  Boolean negation exchanges them and no
minimizer is fixed.  Their intersection is unacceptable, while their union is
the full family.

This is a fully explicit finite countermodel to the inference

  existence of a cardinal-minimal acceptable family
    => canonical symmetry-compatible single choice.

The corresponding ideal-theoretic model over Z is recorded in the machine
counterexample ledger: (6) is contained in both (2) and (3), but the sum of the
two candidate ideals is the unit ideal.
-/

namespace PCRLean
namespace Experimental
namespace TwoChoiceMarkedMinimizerNoGo

open CanonicalMarkedMinimizerSpace

/-- Acceptance means that at least one correction component is selected. -/
def Acceptable (selected : Finset Bool) : Prop := selected.Nonempty

/-- Every singleton is a minimizer. -/
theorem singleton_isMinimizer (b : Bool) :
    IsMinimizer Acceptable {b} := by
  constructor
  · exact ⟨b, by simp⟩
  · intro other hother
    have hpos : 0 < other.card := Finset.card_pos.mpr hother
    simpa using hpos

/-- Every minimizer has exactly one element. -/
theorem card_eq_one_of_minimizer
    {selected : Finset Bool}
    (hselected : IsMinimizer Acceptable selected) :
    selected.card = 1 := by
  have hle : selected.card ≤ ({true} : Finset Bool).card :=
    hselected.2 {true} ⟨true, by simp⟩
  have hpos : 0 < selected.card := Finset.card_pos.mpr hselected.1
  omega

/-- The two singleton subsets are exactly all minimizers. -/
theorem minimizer_iff
    (selected : Finset Bool) :
    IsMinimizer Acceptable selected ↔
      selected = {false} ∨ selected = {true} := by
  constructor
  · intro hselected
    rcases Finset.card_eq_one.mp (card_eq_one_of_minimizer hselected) with
      ⟨b, rfl⟩
    cases b <;> simp
  · rintro (rfl | rfl)
    · exact singleton_isMinimizer false
    · exact singleton_isMinimizer true

/-- Boolean negation as the symmetry exchanging the two components. -/
def swap : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

@[simp] theorem swap_false : swap false = true := rfl
@[simp] theorem swap_true : swap true = false := rfl

/-- The symmetry exchanges the two minimizers. -/
theorem map_false_eq_true :
    ({false} : Finset Bool).map swap.toEmbedding = {true} := by
  simp [swap]

/-- The symmetry exchanges the two minimizers in the other direction. -/
theorem map_true_eq_false :
    ({true} : Finset Bool).map swap.toEmbedding = {false} := by
  simp [swap]

/-- No symmetry-fixed cardinal-minimal acceptable family exists. -/
theorem no_equivariant_single_minimizer :
    ¬ ∃ selected : Finset Bool,
      IsMinimizer Acceptable selected ∧
        selected.map swap.toEmbedding = selected := by
  apply no_fixed_minimizer_of_two_point_swap
    (Acceptable := Acceptable)
    (U := ({false} : Finset Bool))
    (V := ({true} : Finset Bool))
    (by simp)
    swap
    map_false_eq_true
    map_true_eq_false
  intro W hW
  exact (minimizer_iff W).mp hW

/-- Intersecting all minimizers destroys acceptability. -/
theorem intersection_not_acceptable :
    ¬ Acceptable (({false} : Finset Bool) ∩ {true}) := by
  simp [Acceptable]

/-- Unioning all minimizers gives the entire component family. -/
theorem union_eq_univ :
    ({false} : Finset Bool) ∪ {true} = Finset.univ := by
  ext b
  cases b <;> simp

end TwoChoiceMarkedMinimizerNoGo
end Experimental
end PCRLean
