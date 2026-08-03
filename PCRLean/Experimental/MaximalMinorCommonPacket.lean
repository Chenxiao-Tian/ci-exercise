import Mathlib
import PCRLean.Experimental.MaximalMinorAtlas
import PCRLean.Experimental.FittingLinearSystemCommonPacket

/-!
# A rectangular affine packet as a canonical maximal-minor common atlas

A finite rectangular affine system consists of

`M : κ × ι → R`,
`b : κ → R`.

If the maximal row minors of `M` generate the unit ideal, the canonical chart
type is all row selections `s : ι → κ`.  On chart `s`, the selected square
matrix and right-hand side are obtained by base change to the away localization
of the selected determinant.

The determinant normalization required by the common-packet compiler follows
from `RingHom.map_det`; no chart matrices, selected rows or determinant
identities are supplied separately.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorCommonPacket

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open MaximalMinorAtlas

variable (M : Matrix κ ι R)
variable (b : κ → R)
variable (H : FullRankCover M)

/-- Canonical determinant atlas. -/
noncomputable def atlas :
    FittingMinorAtlas.Atlas
      (R := R) (Chart := Selection (κ := κ) (ι := ι)) :=
  H.toAtlas

/-- Right-hand side selected by one maximal minor. -/
def selectedRhs
    (s : Selection (κ := κ) (ι := ι)) : ι → R :=
  fun i => b (s i)

/-- Canonical common-packet data. -/
noncomputable def data :
    FittingLinearSystemCommonPacket.Data
      (R := R) (ι := ι) (κ := κ) H.toAtlas where
  matrix := M
  rhs := b
  selectedRow := fun s => s
  det_eq := by
    intro s
    have hmap := RingHom.map_det
      (algebraMap R
        (FittingGraphCentreAtlas.ChartRing H.toAtlas s))
      (selectedMatrix M s)
    simpa [FittingLinearSystemCommonPacket.Data.localMatrix,
      selectedMatrix, determinant] using hmap.symm

/-- The local square matrix is coefficientwise base change of the selected
maximal minor. -/
theorem localMatrix_apply
    (s : Selection (κ := κ) (ι := ι)) (i j : ι) :
    (data M b H).localMatrix s i j =
      algebraMap R
        (FittingGraphCentreAtlas.ChartRing H.toAtlas s)
        (M (s i) j) :=
  rfl

/-- The local right-hand side is the base change of the selected entries. -/
theorem localRhs_apply
    (s : Selection (κ := κ) (ι := ι)) (i : ι) :
    (data M b H).localRhs s i =
      algebraMap R
        (FittingGraphCentreAtlas.ChartRing H.toAtlas s)
        (b (s i)) :=
  rfl

/-- The canonical system atlas has unit determinant on every chart. -/
theorem local_det_isUnit
    (s : Selection (κ := κ) (ι := ι)) :
    IsUnit ((data M b H).localMatrix s).det :=
  (data M b H).toSystemAtlas.det_isUnit s

end

end MaximalMinorCommonPacket
end Experimental
end PCRLean
