import Mathlib

/-!
# Crossing source centres require arrangement completion

Two preparatory source centres attached to different carriers can meet without
being disjoint or nested.  The finite-set model `{0,1}` and `{1,2}` is the
smallest combinatorial witness.  Their intersection `{1}` is a new deeper
stratum contained in both.

The model does not claim that every finite-set arrangement is geometric.  It
serves only as a no-go leaf against an algorithm that independently legalizes
maximal carriers while ignoring intersections of their preparatory source
centres.
-/

namespace PCRLean
namespace Experimental
namespace CrossCarrierCompletionModel

/-- The first crossing source. -/
def D : Finset ℕ := {0, 1}

/-- The second crossing carrier/source. -/
def C : Finset ℕ := {1, 2}

/-- Their new deepest intersection stratum. -/
def E : Finset ℕ := {1}

@[simp] theorem inter_eq : D ∩ C = E := by
  ext x
  simp [D, C, E]

/-- The two raw sources are not disjoint. -/
theorem not_disjoint : ¬ Disjoint D C := by
  rw [Finset.disjoint_iff_inter_eq_empty, inter_eq]
  simp [E]

/-- The first source is not contained in the second. -/
theorem not_D_subset_C : ¬ D ⊆ C := by
  intro h
  have : 0 ∈ C := h (by simp [D])
  simpa [C] using this

/-- The second source is not contained in the first. -/
theorem not_C_subset_D : ¬ C ⊆ D := by
  intro h
  have : 2 ∈ D := h (by simp [C])
  simpa [D] using this

/-- The completed intersection is contained in both crossing sources. -/
theorem E_subset_both : E ⊆ D ∧ E ⊆ C := by
  constructor <;> intro x hx <;> simp [E] at hx <;> subst x <;> simp [D, C]

end CrossCarrierCompletionModel
end Experimental
end PCRLean
