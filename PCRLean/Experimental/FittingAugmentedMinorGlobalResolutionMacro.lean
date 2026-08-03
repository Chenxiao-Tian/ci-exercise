import Mathlib
import PCRLean.Experimental.FittingAugmentedMinorConsistency
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro

/-!
# Global affine resolution macro from Fitting and augmented minors

The input is now a finite common affine linear packet together with:

* a finite family of selected square minors whose determinants cover `Spec R`;
* the equality identifying each selected determinant with its chart
  determinant; and
* vanishing of every selected-plus-one augmented minor.

Schur-complement consistency makes every selected solution satisfy the full
packet.  Consequently all local solutions agree, the affine structure sheaf
glues them to one actual global graph, and the complete global graph macro
supplies active, passive, SNC-sequence, all-chart and causal certificates.

This is the strongest current affine compiler from explicit Fitting data to an
actual resolution step.  The remaining universal bridge is to extract this
finite common linear packet and its determinant identities from the intrinsic
Frobenius/Hasse/Fitting core of an arbitrary resolution state.
-/

namespace PCRLean
namespace Experimental
namespace FittingAugmentedMinorGlobalResolutionMacro

noncomputable section

universe u v w x y z t

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type x} [Fintype κ]
variable {N : Type y} [AddCommGroup N] [Module R N] [Module.Flat R N]
variable {β : Type z} [Fintype β] [DecidableEq β]
variable {Source : Type t} [Fintype Source] [DecidableEq Source]

open FittingLinearSystemCommonPacket
open FittingAugmentedMinorConsistency

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable {D : FittingLinearSystemCommonPacket.Data
  (R := R) (ι := ι) (κ := κ) A}
variable (H : FittingAugmentedMinorConsistency.AugmentedMinorsVanish D)

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Actual global graph extracted from the determinantal packet. -/
noncomputable def globalGraph : ι → R :=
  H.globalGraph

/-- Actual global centre. -/
def globalCentre : Ideal (MvPolynomial ι R) :=
  PolynomialGraphCentreHeredity.graphIdeal H.globalGraph

/-- Full global affine certificate. -/
structure Certificate
    (boundary : β → Ideal R)
    (activeSources : Finset (Finset Source))
    (e mark : Nat) where
  determinantCover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  augmentedConsistency :
    FittingLinearSystemCommonPacket.Data.Consistent D
  globalGraph : ι → R
  globalCentre : Ideal (MvPolynomial ι R)
  localSolution : ∀ c i,
    algebraMap R (FittingGraphCentreAtlas.ChartRing A c)
        (globalGraph i) = D.graph c i
  localEquationIdeal : ∀ c,
    (D.toSystemAtlas.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι)
          (algebraMap R (FittingGraphCentreAtlas.ChartRing A c)))
        globalCentre
  globalMacro :
    PolynomialGraphLocalResolutionMacro.Certificate
      (R := R) (ι := ι) (N := N)
      p globalGraph boundary activeSources e mark

/-- Assemble the complete affine resolution macro from augmented-minor data. -/
noncomputable def certificate
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    Certificate (R := R) (N := N) H p
      boundary activeSources e mark where
  determinantCover := A.basicOpen_cover
  augmentedConsistency := H.toConsistent
  globalGraph := H.globalGraph
  globalCentre := H.globalCentre
  localSolution := H.globalGraph_localizes
  localEquationIdeal := H.localEquationIdeal_is_globalCentreBaseChange
  globalMacro :=
    FittingGraphGlobalResolutionMacro.certificate
      (R := R) (N := N) H.toGraphCompatible p
      boundary hboundary activeSources e mark
      hmark_pos hmark_le |>.globalMacro

/-- Every local selected-system ideal is the base change of one actual global
centre. -/
theorem allLocalSystemIdeals_fromGlobal (c : Chart) :
    (D.toSystemAtlas.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι)
          (algebraMap R (FittingGraphCentreAtlas.ChartRing A c)))
        H.globalCentre :=
  H.localEquationIdeal_is_globalCentreBaseChange c

end

end FittingAugmentedMinorGlobalResolutionMacro
end Experimental
end PCRLean
