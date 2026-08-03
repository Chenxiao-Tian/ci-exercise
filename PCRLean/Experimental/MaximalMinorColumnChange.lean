import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PCRLean.Experimental.MaximalMinorRangeCriterion

/-!
# Invariance under invertible normal-coordinate changes

Let `M : κ × ι → R` and let `V : ι × ι → R` have unit determinant.  Replacing
normal coordinates by `z = V y` replaces the packet matrix by `M V`.

This module proves directly that:

* every selected maximal minor is multiplied by `det V`;
* hence maximal minors generate the unit ideal for `M V` whenever they do for
  `M`;
* `M z = b` is solvable iff `(M V) y = b` is solvable;
* the augmented-minor criterion is invariant; and
* the two globally glued solutions are related by `z = V y`.

Thus the finite determinantal centre compiler is natural under arbitrary
invertible changes of the normal-coordinate frame.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorColumnChange

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MaximalMinorAtlas
open MaximalMinorAugmentedPacket

variable (M : Matrix κ ι R)
variable (b : κ → R)
variable (V : Matrix ι ι R)
variable (hV : IsUnit V.det)

/-- Selected maximal minors commute with right multiplication. -/
theorem selectedMatrix_mul_right
    (s : Selection (κ := κ) (ι := ι)) :
    selectedMatrix (M * V) s = selectedMatrix M s * V := by
  ext i j
  simp [selectedMatrix, Matrix.mul_apply]

/-- Every transformed maximal minor is the old minor times `det V`. -/
theorem determinant_mul_right
    (s : Selection (κ := κ) (ι := ι)) :
    determinant (M * V) s = determinant M s * V.det := by
  rw [determinant, selectedMatrix_mul_right M V s,
    Matrix.det_mul]

/-- An invertible normal-coordinate change preserves the full-rank Fitting
cover. -/
noncomputable def fullRankCover
    (Hrank : FullRankCover M) :
    FullRankCover (M * V) where
  cover := by
    apply top_unique
    rw [← Hrank.cover, Ideal.span_le]
    rintro x ⟨s, rfl⟩
    have hnew : determinant (M * V) s ∈
        Ideal.span (Set.range (determinant (M * V))) :=
      Ideal.subset_span ⟨s, rfl⟩
    have hscaled :=
      (Ideal.span (Set.range (determinant (M * V)))).mul_mem_left
        ((hV.unit⁻¹ : Rˣ) : R) hnew
    rw [determinant_mul_right M V s] at hscaled
    simpa [hV.unit_spec, mul_assoc] using hscaled

/-- Forward transport of an actual solution. -/
theorem solution_forward
    {y : ι → R}
    (hy : (M * V).mulVec y = b) :
    M.mulVec (V.mulVec y) = b := by
  simpa [Matrix.mulVec_mulVec] using hy

/-- Inverse transport of an actual solution. -/
theorem solution_backward
    {z : ι → R}
    (hz : M.mulVec z = b) :
    (M * V).mulVec (V⁻¹.mulVec z) = b := by
  calc
    (M * V).mulVec (V⁻¹.mulVec z) =
        M.mulVec ((V * V⁻¹).mulVec z) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = M.mulVec z := by
      rw [Matrix.mul_nonsing_inv V hV]
      simp
    _ = b := hz

/-- Solvability is invariant under the normal-coordinate change. -/
theorem exists_solution_iff :
    (∃ z : ι → R, M.mulVec z = b) ↔
      ∃ y : ι → R, (M * V).mulVec y = b := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨V⁻¹.mulVec z, solution_backward M b V hV hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨V.mulVec y, solution_forward M b V hy⟩

variable (Hrank : FullRankCover M)

/-- The maximal-plus-augmented minor condition is invariant under an invertible
normal-coordinate change. -/
theorem augmentedRankCondition_iff :
    AugmentedRankCondition M b ↔
      AugmentedRankCondition (M * V) b := by
  rw [MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        M b Hrank,
      MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        (M * V) b (fullRankCover M V hV Hrank)]
  exact exists_solution_iff M b V hV

/-- Transport an augmented-minor certificate to the transformed packet. -/
noncomputable def transportAugmented
    (Haug : AugmentedRankCondition M b) :
    AugmentedRankCondition (M * V) b :=
  (augmentedRankCondition_iff M b V hV Hrank).mp Haug

/-- The transformed global graph is the inverse-coordinate image of the old
one. -/
theorem transformed_globalGraph_eq
    (Haug : AugmentedRankCondition M b) :
    (transportAugmented M b V hV Hrank Haug).globalGraph
        (fullRankCover M V hV Hrank) =
      V⁻¹.mulVec (Haug.globalGraph Hrank) := by
  let HaugV := transportAugmented M b V hV Hrank Haug
  apply HaugV.solution_eq_globalGraph
    (fullRankCover M V hV Hrank)
  exact solution_backward M b V hV
    (Haug.globalGraph_solves Hrank)

/-- Equivalent forward form of the global graph transport. -/
theorem mulVec_transformed_globalGraph
    (Haug : AugmentedRankCondition M b) :
    V.mulVec
      ((transportAugmented M b V hV Hrank Haug).globalGraph
        (fullRankCover M V hV Hrank)) =
      Haug.globalGraph Hrank := by
  rw [transformed_globalGraph_eq M b V hV Hrank Haug,
    ← Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv V hV]
  simp

end

end MaximalMinorColumnChange
end Experimental
end PCRLean
