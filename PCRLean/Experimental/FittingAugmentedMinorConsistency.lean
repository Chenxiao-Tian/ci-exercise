import Mathlib
import PCRLean.Experimental.AugmentedMinorConsistency
import PCRLean.Experimental.FittingLinearSystemCommonPacket

/-!
# Fitting consistency from vanishing augmented minors

A selected determinant chart provides an invertible square subsystem of a
common finite affine equation packet. For every full equation row, append that
row and its right-hand side to the selected subsystem. If the resulting
augmented determinant vanishes, the Schur-complement theorem says that the
selected graph solution satisfies the extra equation.

Vanishing of all such augmented minors therefore proves that every local
selected-minor solution satisfies the complete packet. The common-packet
compiler then gives overlap compatibility, an actual global graph centre and
the complete global affine graph macro.

This is the precise determinantal bridge from Fitting data to graph centres.
The remaining extraction problem is to show that the Frobenius/Hasse/Fitting
core canonically supplies the common linear packet, selected minors, and the
augmented-minor vanishing identities.
-/

namespace PCRLean
namespace Experimental
namespace FittingAugmentedMinorConsistency

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type x} [Fintype κ]

open FittingGraphCentreAtlas
open FittingLinearSystemCommonPacket

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable (D : FittingLinearSystemCommonPacket.Data
  (R := R) (ι := ι) (κ := κ) A)

/-- Full equation row after localization to one chart. -/
def localFullRow (c : Chart) (r : κ) : ι → ChartRing A c :=
  fun j => algebraMap R (ChartRing A c) (D.matrix r j)

/-- Full right-hand side after localization. -/
def localFullRhs (c : Chart) (r : κ) : ChartRing A c :=
  algebraMap R (ChartRing A c) (D.rhs r)

/-- The graph selected from one determinant minor is the Schur selected-system
solution. -/
theorem graph_eq_selectedSolution (c : Chart) :
    D.graph c =
      AugmentedMinorConsistency.solution
        (D.localMatrix c) (D.localRhs c) := by
  rfl

/-- Vanishing of every selected-plus-one augmented minor. -/
structure AugmentedMinorsVanish : Prop where
  det_zero : ∀ c : Chart, ∀ r : κ,
    (AugmentedMinorConsistency.augmented
      (D.localMatrix c) (D.localRhs c)
      (D.localFullRow c r) (D.localFullRhs c r)).det = 0

namespace AugmentedMinorsVanish

variable (H : D.AugmentedMinorsVanish)

/-- Every selected-minor solution satisfies every row of the common packet. -/
theorem fullEquation (c : Chart) (r : κ) :
    D.fullEquationValue c r =
      algebraMap R (ChartRing A c) (D.rhs r) := by
  have heq :=
    AugmentedMinorConsistency.equation_of_det_augmented_eq_zero
      (D.localMatrix c) (D.localRhs c)
      (D.localFullRow c r) (D.localFullRhs c r)
      (D.toSystemAtlas.det_isUnit c)
      (H.det_zero c r)
  rw [← D.graph_eq_selectedSolution c] at heq
  simpa [FittingLinearSystemCommonPacket.Data.fullEquationValue,
    localFullRow, localFullRhs, dotProduct] using heq

/-- Compile augmented-minor vanishing into complete packet consistency. -/
noncomputable def toConsistent : D.Consistent where
  fullEquation := H.fullEquation

/-- Hence all selected-minor graph solutions agree on every overlap. -/
noncomputable def toGraphCompatible :
    FittingGraphCentreOverlap.Compatible
      D.toSystemAtlas.toGraphAtlasData :=
  H.toConsistent.toGraphCompatible

/-- Actual global graph tuple determined by the determinantal packet. -/
noncomputable def globalGraph : ι → R :=
  H.toConsistent.globalGraph

/-- Every local selected subsystem solution is the localization of the global
solution. -/
theorem globalGraph_localizes (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c) (H.globalGraph i) =
      D.graph c i :=
  H.toConsistent.globalGraph_localizes c i

/-- Every local selected-system ideal is the base change of the same global
graph centre. -/
theorem localEquationIdeal_is_globalCentreBaseChange (c : Chart) :
    (D.toSystemAtlas.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal H.globalGraph) :=
  H.toConsistent.localEquationIdeal_is_globalCentreBaseChange c

end AugmentedMinorsVanish

end

end FittingAugmentedMinorConsistency
end Experimental
end PCRLean
