import Mathlib
import PCRLean.Experimental.ModuleImageCentre
import PCRLean.Experimental.HeterogeneousGeneratorGluing
import PCRLean.Experimental.FittingGraphCentreAtlas

/-!
# Global module-image centres with local Fitting graph models

Let `φ : M →ₗ[R] R` be a global finite-module morphism and let

`C = image(φ) ⊂ R`.

Choose one finite spanning frame of `M`.  On every determinant chart, map the
resulting global equation vector to the localization.  A local graph frame may
have a different number of equations; it is required only to be mutually
expressible by finite linear combinations with the mapped global frame.

The heterogeneous generator theorem then proves

`graphIdeal(h_c) = C · R_{d_c}`.

Thus all local graph centres are base changes of one pre-existing actual global
ideal.  No global graph tuple, global conormal basis, or equality of local graph
coordinates is needed.  Fitting charts are used only to certify the local
regular graph form.

The remaining universal extraction theorem must construct `M`, `φ`, its finite
frame, and the local frame-equivalence certificates from the intrinsic
Frobenius/Hasse/Fitting state.
-/

namespace PCRLean
namespace Experimental
namespace ModuleImageGraphAtlas

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {μ : Type w} [Fintype μ]
variable {Chart : Type x} [Fintype Chart]
variable {ι : Type y} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open FittingGraphCentreAtlas

variable (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
variable (φ : M →ₗ[R] R)
variable (F : ModuleImageCentre.SpanningFrame
  (R := R) (M := M) (ι := μ))

/-- The intrinsic actual global centre. -/
def globalCentre : Ideal R := ModuleImageCentre.imageIdeal φ

/-- Global frame equations mapped to one determinant chart. -/
def mappedGlobalEquation (c : Chart) : μ → ChartRing A c :=
  fun a => algebraMap R (ChartRing A c) (F.equation φ a)

/-- Local graph data together with finite presentation changes identifying it
with the global image ideal. -/
structure Data where
  graph : ∀ c : Chart, ι → ChartRing A c
  frameEquiv : ∀ c : Chart,
    HeterogeneousGeneratorGluing.FrameEquivalence
      (mappedGlobalEquation A φ F c)
      (PolynomialGraphCentreHeredity.graphGenerator (graph c))

namespace Data

variable (D : Data (ι := ι) A φ F)

/-- Local graph ideal. -/
def localCentre (c : Chart) : Ideal (ChartRing A c) :=
  PolynomialGraphCentreHeredity.graphIdeal (D.graph c)

/-- Every local graph centre is exactly the base change of the global image
centre. -/
theorem localCentre_eq_map_globalCentre (c : Chart) :
    D.localCentre c =
      Ideal.map (algebraMap R (ChartRing A c))
        (globalCentre φ) := by
  calc
    D.localCentre c =
        ActualIdealGluing.generatedIdeal
          (PolynomialGraphCentreHeredity.graphGenerator (D.graph c)) := rfl
    _ = ActualIdealGluing.generatedIdeal
          (mappedGlobalEquation A φ F c) :=
      (D.frameEquiv c).ideal_eq.symm
    _ = Ideal.map (algebraMap R (ChartRing A c))
          (globalCentre φ) := by
      symm
      exact F.map_imageIdeal_eq_generatedIdeal φ

/-- Derived ordinary graph-atlas data. -/
noncomputable def toGraphAtlasData :
    GraphAtlasData (ι := ι) A where
  graph := D.graph

/-- Every chart has an actual regular graph-centre certificate. -/
noncomputable def localRegularCertificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (c : Chart) (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (D.graph c) e :=
  PolynomialGraphFrobeniusCentreCertificate.certificate
    p (D.graph c) e

/-- Complete finite local-model certificate for the global image centre. -/
structure Certificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e : Nat) where
  globalCentre : Ideal R
  globalCentre_eq : globalCentre = ModuleImageCentre.imageIdeal φ
  globalFiniteType : globalCentre.FG
  determinantCover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  localGraph : ∀ c : Chart, ι → ChartRing A c
  localFromGlobal : ∀ c : Chart,
    PolynomialGraphCentreHeredity.graphIdeal (localGraph c) =
      Ideal.map (algebraMap R (ChartRing A c)) globalCentre
  localRegular : ∀ c : Chart,
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (localGraph c) e

/-- Assemble the global-image/local-graph certificate. -/
noncomputable def certificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e : Nat) : Certificate A φ F D p e where
  globalCentre := globalCentre φ
  globalCentre_eq := rfl
  globalFiniteType := F.imageIdeal_fg φ
  determinantCover := A.basicOpen_cover
  localGraph := D.graph
  localFromGlobal := D.localCentre_eq_map_globalCentre
  localRegular := D.localRegularCertificate p

end Data

end

end ModuleImageGraphAtlas
end Experimental
end PCRLean
