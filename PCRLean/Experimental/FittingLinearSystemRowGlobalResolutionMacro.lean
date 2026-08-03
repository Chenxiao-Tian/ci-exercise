import Mathlib
import PCRLean.Experimental.FittingLinearSystemRowCompatibility
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro

/-!
# Global affine resolution from row-compatible Fitting systems

Local equation frames are rarely literally equal on overlaps.  They are
related by row operations.  The row-compatibility theorem already proves that
such systems have the same graph solution on every overlap.

This module compiles that presentation-independent compatibility directly to:

* one actual global graph tuple;
* one global actual centre ideal;
* exact recovery of every local equation ideal by base change; and
* the full global affine graph resolution macro.

No graph tuple, local centre ideal or invertible row matrix is used after the
system compatibility proof.  The remaining extraction problem is to obtain the
finite row-compatible determinant-normalized system atlas from the intrinsic
Frobenius/Hasse/Fitting object.
-/

namespace PCRLean
namespace Experimental
namespace FittingLinearSystemRowGlobalResolutionMacro

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
open FittingLinearSystemRowCompatibility

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
variable {D : FittingLinearSystemAtlas.Data (ι := ι) A}
variable (H : FittingLinearSystemRowCompatibility.Compatible D)

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Actual global graph from row-compatible local systems. -/
noncomputable def globalGraph : ι → R :=
  H.globalGraph

/-- Actual global centre. -/
def globalCentre : Ideal (MvPolynomial ι R) :=
  PolynomialGraphCentreHeredity.graphIdeal H.globalGraph

/-- Full global affine macro certificate. -/
structure Certificate
    (boundary : β → Ideal R)
    (activeSources : Finset (Finset Source))
    (e mark : Nat) where
  determinantCover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  globalGraph : ι → R
  globalCentre : Ideal (MvPolynomial ι R)
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

/-- Assemble the global macro from row-compatible systems. -/
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
  localSolution := H.globalGraph_localizes
  localEquationIdeal := H.localEquationIdeal_is_globalCentreBaseChange
  globalMacro :=
    FittingGraphGlobalResolutionMacro.certificate
      (R := R) (N := N) H.toGraphCompatible p
      boundary hboundary activeSources e mark
      hmark_pos hmark_le |>.globalMacro

/-- Every local system ideal is the base change of the same global centre. -/
theorem allLocalSystemIdeals_fromGlobal (c : Chart) :
    (D.localSystem c).equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        H.globalCentre :=
  H.localEquationIdeal_is_globalCentreBaseChange c

end

end FittingLinearSystemRowGlobalResolutionMacro
end Experimental
end PCRLean
