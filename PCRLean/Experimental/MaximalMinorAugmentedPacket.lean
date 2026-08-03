import Mathlib
import PCRLean.Experimental.MaximalMinorCommonPacket
import PCRLean.Experimental.FittingAugmentedMinorConsistency

/-!
# Canonical maximal and augmented minor conditions

For a finite rectangular affine packet `M z = b`, two finite determinantal
conditions are singled out:

1. the maximal row minors of `M` generate the unit ideal;
2. for every maximal row selection and every equation row, the corresponding
   selected-plus-one augmented determinant is zero.

The first condition gives the canonical finite determinant cover. The second,
after localization and `RingHom.map_det`, gives the augmented-minor vanishing
hypothesis of the Schur consistency compiler.

Thus the two global determinantal conditions automatically yield complete
local-packet consistency, graph overlap compatibility and one actual global
graph centre.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorAugmentedPacket

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MaximalMinorAtlas

variable (M : Matrix κ ι R)
variable (b : κ → R)
variable (Hrank : FullRankCover M)

/-- Right-hand side of one selected subsystem over the base ring. -/
def selectedRhs
    (s : Selection (κ := κ) (ι := ι)) : ι → R :=
  fun i => b (s i)

/-- One full equation row. -/
def fullRow (r : κ) : ι → R :=
  fun j => M r j

/-- One selected-plus-one augmented matrix over `R`. -/
def augmentedMatrix
    (s : Selection (κ := κ) (ι := ι)) (r : κ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  AugmentedMinorConsistency.augmented
    (selectedMatrix M s) (selectedRhs b s)
    (fullRow M r) (b r)

/-- All maximal selected-plus-one augmented minors vanish. -/
structure AugmentedRankCondition : Prop where
  det_zero : ∀ s : Selection (κ := κ) (ι := ι), ∀ r : κ,
    (augmentedMatrix M b s r).det = 0

namespace AugmentedRankCondition

variable (Haug : AugmentedRankCondition M b)

/-- Coefficientwise base change of the global augmented matrix is exactly the
local augmented matrix used by the Schur compiler. -/
theorem map_augmentedMatrix_eq_local
    (s : Selection (κ := κ) (ι := ι)) (r : κ) :
    (algebraMap R
      (FittingGraphCentreAtlas.ChartRing Hrank.toAtlas s)).mapMatrix
        (augmentedMatrix M b s r) =
      AugmentedMinorConsistency.augmented
        ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s)
        ((MaximalMinorCommonPacket.data M b Hrank).localRhs s)
        (FittingAugmentedMinorConsistency.localFullRow
          (MaximalMinorCommonPacket.data M b Hrank) s r)
        (FittingAugmentedMinorConsistency.localFullRhs
          (MaximalMinorCommonPacket.data M b Hrank) s r) := by
  ext x y
  rcases x with i | u <;> rcases y with j | v <;>
    simp [augmentedMatrix, AugmentedMinorConsistency.augmented,
      AugmentedMinorConsistency.column, AugmentedMinorConsistency.row,
      AugmentedMinorConsistency.scalar, selectedRhs, fullRow,
      MaximalMinorCommonPacket.data,
      FittingLinearSystemCommonPacket.Data.localMatrix,
      FittingLinearSystemCommonPacket.Data.localRhs,
      FittingAugmentedMinorConsistency.localFullRow,
      FittingAugmentedMinorConsistency.localFullRhs,
      selectedMatrix]

/-- Every global augmented-minor identity remains zero on its determinant
chart. -/
theorem local_augmented_det_zero
    (s : Selection (κ := κ) (ι := ι)) (r : κ) :
    (AugmentedMinorConsistency.augmented
      ((MaximalMinorCommonPacket.data M b Hrank).localMatrix s)
      ((MaximalMinorCommonPacket.data M b Hrank).localRhs s)
      (FittingAugmentedMinorConsistency.localFullRow
        (MaximalMinorCommonPacket.data M b Hrank) s r)
      (FittingAugmentedMinorConsistency.localFullRhs
        (MaximalMinorCommonPacket.data M b Hrank) s r)).det = 0 := by
  let f := algebraMap R
    (FittingGraphCentreAtlas.ChartRing Hrank.toAtlas s)
  have hmap := RingHom.map_det f (augmentedMatrix M b s r)
  have hmapped :
      (f.mapMatrix (augmentedMatrix M b s r)).det = 0 := by
    rw [← hmap, Haug.det_zero s r]
    simp
  rw [Haug.map_augmentedMatrix_eq_local Hrank s r] at hmapped
  exact hmapped

/-- Compile the two global determinantal conditions into the localized Schur
consistency interface. -/
noncomputable def toAugmentedMinorsVanish :
    FittingAugmentedMinorConsistency.AugmentedMinorsVanish
      (MaximalMinorCommonPacket.data M b Hrank) where
  det_zero := Haug.local_augmented_det_zero Hrank

/-- Hence the canonical maximal-minor atlas is fully consistent. -/
noncomputable def toConsistent :
    FittingLinearSystemCommonPacket.Data.Consistent
      (MaximalMinorCommonPacket.data M b Hrank) :=
  Haug.toAugmentedMinorsVanish Hrank |>.toConsistent

/-- Actual global graph tuple extracted from the two determinantal conditions. -/
noncomputable def globalGraph : ι → R :=
  Haug.toAugmentedMinorsVanish Hrank |>.globalGraph

/-- Every selected-minor graph is the localization of the global graph. -/
theorem globalGraph_localizes
    (s : Selection (κ := κ) (ι := ι)) (i : ι) :
    algebraMap R
        (FittingGraphCentreAtlas.ChartRing Hrank.toAtlas s)
        (Haug.globalGraph Hrank i) =
      (MaximalMinorCommonPacket.data M b Hrank).graph s i :=
  Haug.toAugmentedMinorsVanish Hrank |>.globalGraph_localizes s i

end AugmentedRankCondition

end

end MaximalMinorAugmentedPacket
end Experimental
end PCRLean
