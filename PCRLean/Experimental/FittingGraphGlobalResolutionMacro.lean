import Mathlib
import PCRLean.Experimental.FittingGraphRestrictionCompatibility
import PCRLean.Experimental.PolynomialGraphLocalResolutionMacro

/-!
# A global affine resolution macro from a compatible Fitting graph atlas

A finite determinant family covers `Spec R`.  Suppose every determinant chart
carries a polynomial graph presentation and the graph tuples agree in every
explicit double localization.  The localization-to-structure-sheaf comparison
and Čech effectivity produce one actual global graph tuple

`h : ι → R`.

The local graph ideals are exactly the base changes of the global ideal

`I_h = (Z_i-h_i) ⊂ R[Z_i]`.

This file then applies the complete polynomial-graph local resolution macro to
that global centre.  The output simultaneously contains:

* a global actual proper finite-type regular centre;
* arbitrary-mark active permissibility;
* induced-flat passive Tor safety and flat centre restriction;
* regular intersections and regular-sequence transport for finite boundary
  strata;
* every standard blowup chart;
* terminality or pure exceptional debt; and
* source-conservative strict causal rank descent.

Thus, conditional on finite Fitting graph data and pairwise overlap equality,
the entire affine gluing problem is closed.  The remaining universal bridge is
to extract such compatible graph data from an arbitrary Frobenius/Hasse/Fitting
core and to globalize beyond one affine ambient chart.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphGlobalResolutionMacro

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
open FittingGraphCentreOverlap
open FittingGraphRestrictionCompatibility

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable {D : GraphAtlasData (ι := ι) A}
variable (H : FittingGraphCentreOverlap.Compatible D)

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- The actual global graph produced by the finite compatible atlas. -/
noncomputable def globalGraph : ι → R :=
  H.toCompatibleSectionData.globalGraph

/-- The actual global graph centre. -/
def globalCentre : Ideal (MvPolynomial ι R) :=
  PolynomialGraphCentreHeredity.graphIdeal (H.globalGraph)

/-- Full global affine certificate. -/
structure Certificate
    (boundary : β → Ideal R)
    (activeSources : Finset (Finset Source))
    (e mark : Nat) where
  determinantCover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  globalGraph : ι → R
  globalCentre : Ideal (MvPolynomial ι R)
  centre_eq : globalCentre =
    PolynomialGraphCentreHeredity.graphIdeal globalGraph
  localGraph : ∀ c i,
    algebraMap R (ChartRing A c) (globalGraph i) = D.graph c i
  localCentre : ∀ c,
    PolynomialGraphCentreHeredity.graphIdeal (D.graph c) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        globalCentre
  globalMacro :
    PolynomialGraphLocalResolutionMacro.Certificate
      (R := R) (ι := ι) (N := N)
      p globalGraph boundary activeSources e mark

/-- Assemble the global affine graph-centre macro. -/
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
  globalGraph := H.globalGraph
  globalCentre := H.globalCentre
  centre_eq := rfl
  localGraph := H.globalGraph_localizes
  localCentre := by
    intro c
    exact H.local_centre_is_global_baseChange c
  globalMacro :=
    PolynomialGraphLocalResolutionMacro.certificate
      (R := R) (ι := ι) (N := N)
      p H.globalGraph boundary hboundary
      activeSources e mark hmark_pos hmark_le

/-- The determinant atlas therefore produces one actual global regular centre,
not merely compatible local ideals. -/
noncomputable def actualGlobalCentreCertificate
    (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p H.globalGraph e :=
  PolynomialGraphFrobeniusCentreCertificate.certificate
    p H.globalGraph e

/-- Every chart-local candidate centre is the base change of the same global
actual ideal. -/
theorem allLocalCentres_fromGlobal (c : Chart) :
    PolynomialGraphCentreHeredity.graphIdeal (D.graph c) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        H.globalCentre :=
  H.local_centre_is_global_baseChange c

end

end FittingGraphGlobalResolutionMacro
end Experimental
end PCRLean
