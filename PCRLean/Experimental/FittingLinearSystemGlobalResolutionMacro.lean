import Mathlib
import PCRLean.Experimental.FittingLinearSystemOverlap
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro

/-!
# A global affine resolution macro from compatible Fitting linear systems

Input data now consists only of:

* a finite determinant family covering `Spec R`;
* on every determinant chart, a square affine linear system whose determinant
  is the distinguished determinant; and
* equality of the matrices and right-hand sides on every double localization.

The determinant makes every local system uniquely solvable. Compatibility of
the systems therefore forces compatibility of the graph solutions. The affine
structure sheaf glues those solutions to one actual global graph tuple and one
global graph centre. Finally, the complete global graph macro supplies active,
passive, boundary, all-chart and causal certificates.

Thus no graph tuple, local centre ideal or overlap ideal equality is an
independent hypothesis. The remaining universal extraction theorem must build
this finite compatible linear-system atlas from the intrinsic
Frobenius/Hasse/Fitting core.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemGlobalResolutionMacro

noncomputable section

universe u v w x y z

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {N : Type x} [AddCommGroup N] [Module R N] [Module.Flat R N]
variable {β : Type y} [Fintype β] [DecidableEq β]
variable {Source : Type z} [Fintype Source] [DecidableEq Source]

open FittingGraphCentreAtlas
open FittingLinearSystemAtlas
open FittingLinearSystemOverlap

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable {D : FittingLinearSystemAtlas.Data (ι := ι) A}
variable (H : FittingLinearSystemOverlap.Compatible D)

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Derived graph compatibility. -/
noncomputable def graphCompatible :
    FittingGraphCentreOverlap.Compatible D.toGraphAtlasData :=
  H.toGraphCompatible

/-- Actual global graph produced by the compatible linear systems. -/
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
  localSystems : ∀ c : Chart,
    DetUnitLinearSystemGraph.System
      (R := ChartRing A c) (ι := ι)
  globalGraph : ι → R
  globalCentre : Ideal (MvPolynomial ι R)
  centre_eq : globalCentre =
    PolynomialGraphCentreHeredity.graphIdeal globalGraph
  localSolution : ∀ c i,
    algebraMap R (ChartRing A c) (globalGraph i) = D.graph c i
  localEquationIdeal : ∀ c,
    (D.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        globalCentre
  globalMacro :
    PolynomialGraphLocalResolutionMacro.Certificate
      (R := R) (ι := ι) (N := N)
      p globalGraph boundary activeSources e mark

/-- Assemble the global affine resolution macro from compatible systems. -/
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
  localSystems := D.localSystem
  globalGraph := H.globalGraph
  globalCentre := H.globalCentre
  centre_eq := rfl
  localSolution := H.globalGraph_localizes
  localEquationIdeal := H.localEquationIdeal_is_globalCentreBaseChange
  globalMacro :=
    FittingGraphGlobalResolutionMacro.certificate
      (R := R) (N := N) H.toGraphCompatible p
      boundary hboundary activeSources e mark
      hmark_pos hmark_le |>.globalMacro

/-- Every local affine system ideal is exactly the base change of the global
actual centre. -/
theorem allLocalSystemIdeals_fromGlobal (c : Chart) :
    (D.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        H.globalCentre :=
  H.localEquationIdeal_is_globalCentreBaseChange c

/-- The global centre receives the complete actual regular-centre certificate. -/
noncomputable def actualGlobalCentreCertificate (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p H.globalGraph e :=
  PolynomialGraphFrobeniusCentreCertificate.certificate
    p H.globalGraph e

end

end FittingLinearSystemGlobalResolutionMacro
end Experimental
end PCRLean
