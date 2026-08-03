import Mathlib
import PCRLean.Experimental.MaximalMinorAugmentedPacket
import PCRLean.Experimental.AugmentedMinorRangeNecessity
import PCRLean.Experimental.FittingMinorFaithfulCover

/-!
# Maximal-minor range criterion

Let `M : κ × ι → R` be a finite rectangular matrix.  Assume its maximal row
minors generate the unit ideal.  Then the map

`z ↦ M.mulVec z`

is injective.  For a right-hand side `b`, the following conditions are
therefore equivalent:

1. all selected-plus-one augmented maximal minors of `[M|b]` vanish;
2. `b` lies in the image of `M.mulVec`;
3. the equation `M z = b` has a unique solution.

The sufficiency direction uses the determinant-chart Schur compiler, affine
Čech effectivity and the jointly faithful finite Fitting cover.  Necessity is
the global column-dependence theorem of
`AugmentedMinorRangeNecessity` and does not use the rank hypothesis.

This is the precise finite determinantal criterion underlying the current
actual-centre synthesis architecture.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorRangeCriterion

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MaximalMinorAtlas
open MaximalMinorAugmentedPacket
open FittingGraphCentreAtlas

variable (M : Matrix κ ι R)
variable (b : κ → R)
variable (Hrank : FullRankCover M)

/-- Coefficientwise localization of a vector to one maximal-minor chart. -/
def localizeVector
    (s : Selection (κ := κ) (ι := ι))
    (z : ι → R) :
    ι → ChartRing Hrank.toAtlas s :=
  fun i => algebraMap R (ChartRing Hrank.toAtlas s) (z i)

/-- A global solution restricts to a solution of every selected square
subsystem. -/
theorem localizeVector_solves_selected
    {z : ι → R}
    (hsol : M.mulVec z = b)
    (s : Selection (κ := κ) (ι := ι)) :
    ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s).mulVec
        (localizeVector M Hrank s z) =
      (MaximalMinorCommonPacket.data M b Hrank).localRhs s := by
  funext i
  have hi := congrArg
    (algebraMap R (ChartRing Hrank.toAtlas s))
    (congrFun hsol (s i))
  simpa [localizeVector, MaximalMinorCommonPacket.data,
    FittingLinearSystemCommonPacket.Data.localMatrix,
    FittingLinearSystemCommonPacket.Data.localRhs,
    Matrix.mulVec, dotProduct] using hi

/-- Every selected square matrix acts injectively on its determinant chart. -/
theorem localMatrix_mulVec_injective
    (s : Selection (κ := κ) (ι := ι)) :
    Function.Injective
      ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s).mulVec := by
  intro x y hxy
  let A := (MaximalMinorCommonPacket.data M b Hrank).localMatrix s
  have h := congrArg A⁻¹.mulVec hxy
  have hinv : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A
      ((MaximalMinorCommonPacket.data M b Hrank).toSystemAtlas.det_isUnit s)
  simpa [A, Matrix.mulVec_mulVec, hinv] using h

/-- Unit generation by maximal minors makes the original rectangular packet
map injective. -/
theorem packet_mulVec_injective :
    Function.Injective M.mulVec := by
  intro x y hxy
  apply Hrank.toAtlas.funext_of_chart_algebraMap_eq
  intro s i
  have hlocal :
      ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s).mulVec
          (localizeVector M Hrank s x) =
        ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s).mulVec
          (localizeVector M Hrank s y) := by
    funext k
    have hk := congrArg
      (algebraMap R (ChartRing Hrank.toAtlas s))
      (congrFun hxy (s k))
    simpa [localizeVector, MaximalMinorCommonPacket.data,
      FittingLinearSystemCommonPacket.Data.localMatrix,
      Matrix.mulVec, dotProduct] using hk
  have hvec := localMatrix_mulVec_injective M b Hrank s hlocal
  exact congrFun hvec i

variable (Haug : AugmentedRankCondition M b)

/-- The graph obtained from augmented-minor consistency solves the complete
global packet, not merely all localized selected subsystems. -/
theorem globalGraph_solves :
    M.mulVec (Haug.globalGraph Hrank) = b := by
  apply Hrank.toAtlas.funext_of_chart_algebraMap_eq
  intro s r
  let D := MaximalMinorCommonPacket.data M b Hrank
  have hlocal := (Haug.toAugmentedMinorsVanish Hrank).fullEquation s r
  calc
    algebraMap R (ChartRing Hrank.toAtlas s)
        (M.mulVec (Haug.globalGraph Hrank) r) =
      ∑ j : ι,
        algebraMap R (ChartRing Hrank.toAtlas s) (M r j) *
          algebraMap R (ChartRing Hrank.toAtlas s)
            (Haug.globalGraph Hrank j) := by
        simp [Matrix.mulVec, dotProduct]
    _ = ∑ j : ι,
        algebraMap R (ChartRing Hrank.toAtlas s) (M r j) *
          D.graph s j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Haug.globalGraph_localizes Hrank s j]
    _ = D.fullEquationValue s r := by
        rfl
    _ = algebraMap R (ChartRing Hrank.toAtlas s) (b r) := by
        simpa [D, MaximalMinorCommonPacket.data] using hlocal

/-- The determinantal global graph is the unique solution of the full packet. -/
theorem solution_eq_globalGraph
    {z : ι → R}
    (hsol : M.mulVec z = b) :
    z = Haug.globalGraph Hrank := by
  apply packet_mulVec_injective M b Hrank
  rw [hsol, Haug.globalGraph_solves Hrank]

/-- Existence and uniqueness supplied by the determinantal conditions. -/
theorem existsUnique_solution :
    ∃! z : ι → R, M.mulVec z = b := by
  refine ⟨Haug.globalGraph Hrank,
    Haug.globalGraph_solves Hrank, ?_⟩
  intro z hz
  exact Haug.solution_eq_globalGraph Hrank hz

/-- Any actual solution forces all global selected-plus-one augmented minors to
vanish.  This direction does not use `Hrank`. -/
theorem augmentedRankCondition_of_solution
    {z : ι → R}
    (hsol : M.mulVec z = b) :
    AugmentedRankCondition M b where
  det_zero := by
    intro s r
    apply AugmentedMinorRangeNecessity.det_augmented_eq_zero_of_solution
      (selectedMatrix M s)
      (selectedRhs b s)
      (fullRow M r)
      z (b r)
    · funext i
      simpa [selectedMatrix, selectedRhs,
        Matrix.mulVec, dotProduct] using congrFun hsol (s i)
    · simpa [fullRow, Matrix.mulVec, dotProduct] using congrFun hsol r

/-- Maximal and augmented minors characterize membership in the image of the
rectangular packet. -/
theorem augmentedRankCondition_iff_exists_solution :
    AugmentedRankCondition M b ↔
      ∃ z : ι → R, M.mulVec z = b := by
  constructor
  · intro H
    exact ⟨H.globalGraph Hrank, H.globalGraph_solves Hrank⟩
  · rintro ⟨z, hz⟩
    exact augmentedRankCondition_of_solution M b hz

/-- Under the full-rank cover, the same finite determinantal conditions are
equivalent to unique solvability. -/
theorem augmentedRankCondition_iff_existsUnique_solution :
    AugmentedRankCondition M b ↔
      ∃! z : ι → R, M.mulVec z = b := by
  constructor
  · intro H
    exact H.existsUnique_solution Hrank
  · rintro ⟨z, hz, hunique⟩
    exact augmentedRankCondition_of_solution M b hz

end

end MaximalMinorRangeCriterion
end Experimental
end PCRLean
