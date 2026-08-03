import Mathlib
import PCRLean.Experimental.FittingMinorAtlas

/-!
# The canonical finite atlas of maximal row minors

Let `M` be a finite rectangular matrix with equation rows indexed by `κ` and
normal coordinates indexed by `ι`.  A maximal row minor is obtained by choosing
one equation row for every normal coordinate, i.e. by a function

`s : ι → κ`.

All such choices form a finite type.  The determinant of the selected square
matrix gives a canonical finite family.  If these determinants generate the
unit ideal, their basic opens cover `Spec R` and on each chart the selected
matrix is invertible.

No arbitrary chart family or determinant list remains in the input.  Repeated
rows simply contribute zero minors and do not affect the cover.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorAtlas

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Canonical finite type of maximal row selections. -/
abbrev Selection := ι → κ

/-- Square matrix selected from the rectangular packet. -/
def selectedMatrix
    (M : Matrix κ ι R) (s : Selection (κ := κ) (ι := ι)) :
    Matrix ι ι R :=
  Matrix.of fun i j => M (s i) j

/-- Determinant of one maximal row selection. -/
def determinant
    (M : Matrix κ ι R) (s : Selection (κ := κ) (ι := ι)) : R :=
  (selectedMatrix M s).det

/-- Maximal minors generate the unit ideal. -/
structure FullRankCover (M : Matrix κ ι R) : Prop where
  cover : Ideal.span (Set.range (determinant M)) = ⊤

namespace FullRankCover

variable {M : Matrix κ ι R}
    (H : FullRankCover M)

/-- Canonical finite Fitting atlas. -/
noncomputable def toAtlas :
    FittingMinorAtlas.Atlas
      (R := R) (Chart := Selection (κ := κ) (ι := ι)) where
  determinant := determinant M
  cover := H.cover

/-- The maximal-minor basic opens cover the whole prime spectrum. -/
theorem basicOpen_cover :
    (⨆ s : Selection (κ := κ) (ι := ι),
      PrimeSpectrum.basicOpen (determinant M s)) = ⊤ :=
  H.toAtlas.basicOpen_cover

/-- Every prime point lies in one maximal-minor chart. -/
theorem point_mem_some_minor (x : PrimeSpectrum R) :
    ∃ s : Selection (κ := κ) (ι := ι),
      x ∈ PrimeSpectrum.basicOpen (determinant M s) :=
  H.toAtlas.point_mem_some_basicOpen x

/-- The chosen minor is a unit in its canonical away localization. -/
theorem determinant_isUnit_away
    (s : Selection (κ := κ) (ι := ι)) :
    IsUnit
      (algebraMap R (Localization.Away (determinant M s))
        (determinant M s)) :=
  H.toAtlas.determinant_isUnit_away s

end FullRankCover

end

end MaximalMinorAtlas
end Experimental
end PCRLean
