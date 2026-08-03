import Mathlib
import PCRLean.Experimental.ModuleImageCentre
import PCRLean.Experimental.HeterogeneousGeneratorGluing
import PCRLean.Experimental.FittingGraphCentreAtlas
import PCRLean.Experimental.PolynomialGraphBaseChange

/-!
# Global module-image centres with local Fitting graph models

Let the global ambient affine ring be

`P = R[Z_i]`.

An intrinsic finite `P`-module morphism

`φ : M →ₗ[P] P`

defines the actual global centre

`C = image(φ) ⊂ P`.

Choose one finite spanning frame of `M`. On every determinant chart of the
coefficient ring `R`, map the resulting global equation vector to
`R_{d_c}[Z_i]`. A locally minimal graph frame may have a different number of
equations; it is required only to be mutually expressible by finite linear
combinations with the mapped global frame.

The heterogeneous generator theorem then proves

`graphIdeal(h_c) = C · R_{d_c}[Z_i]`.

Thus all local graph centres are base changes of one pre-existing actual global
ideal. No global graph tuple, global conormal basis, or equality of local graph
coordinates is needed. Fitting charts are used only to certify the local
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
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev P := MvPolynomial ι R

variable {M : Type w} [AddCommGroup M]
variable [Module (P (R := R) (ι := ι)) M]
variable {μ : Type x} [Fintype μ]
variable {Chart : Type y} [Fintype Chart]

open FittingGraphCentreAtlas

variable (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
variable (φ : M →ₗ[P (R := R) (ι := ι)] P)
variable (F : ModuleImageCentre.SpanningFrame
  (R := P (R := R) (ι := ι)) (M := M) (ι := μ))

/-- Polynomial ambient ring on one determinant chart. -/
abbrev ChartAmbient (c : Chart) :=
  MvPolynomial ι (ChartRing A c)

/-- Coefficientwise base-change map to one chart ambient ring. -/
def chartPolynomialMap (c : Chart) :
    P (R := R) (ι := ι) →+* ChartAmbient (ι := ι) A c :=
  PolynomialGraphBaseChange.polynomialMap
    (ι := ι) (algebraMap R (ChartRing A c))

/-- The intrinsic actual global centre in the global polynomial ambient ring. -/
def globalCentre : Ideal (P (R := R) (ι := ι)) :=
  ModuleImageCentre.imageIdeal φ

/-- Global frame equations mapped to one determinant chart. -/
def mappedGlobalEquation (c : Chart) :
    μ → ChartAmbient (ι := ι) A c :=
  fun a => chartPolynomialMap (ι := ι) A c (F.equation φ a)

/-- Local graph data together with finite presentation changes identifying it
with the global image ideal. -/
structure Data where
  graph : ∀ c : Chart, ι → ChartRing A c
  frameEquiv : ∀ c : Chart,
    HeterogeneousGeneratorGluing.FrameEquivalence
      (mappedGlobalEquation (ι := ι) A φ F c)
      (PolynomialGraphCentreHeredity.graphGenerator (graph c))

namespace Data

variable (D : Data (ι := ι) A φ F)

/-- Local graph ideal in the chart ambient polynomial ring. -/
def localCentre (c : Chart) :
    Ideal (ChartAmbient (ι := ι) A c) :=
  PolynomialGraphCentreHeredity.graphIdeal (D.graph c)

/-- Every local graph centre is exactly the polynomial base change of the
global image centre. -/
theorem localCentre_eq_map_globalCentre (c : Chart) :
    D.localCentre c =
      Ideal.map (chartPolynomialMap (ι := ι) A c)
        (globalCentre φ) := by
  calc
    D.localCentre c =
        ActualIdealGluing.generatedIdeal
          (PolynomialGraphCentreHeredity.graphGenerator (D.graph c)) := rfl
    _ = ActualIdealGluing.generatedIdeal
          (mappedGlobalEquation (ι := ι) A φ F c) :=
      (D.frameEquiv c).ideal_eq.symm
    _ = Ideal.map (chartPolynomialMap (ι := ι) A c)
          (globalCentre φ) := by
      symm
      exact F.map_imageIdeal_eq_generatedIdeal_ringHom
        (chartPolynomialMap (ι := ι) A c) φ

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
  globalCentre : Ideal (P (R := R) (ι := ι))
  globalCentre_eq : globalCentre = ModuleImageCentre.imageIdeal φ
  globalFiniteType : globalCentre.FG
  determinantCover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  localGraph : ∀ c : Chart, ι → ChartRing A c
  localFromGlobal : ∀ c : Chart,
    PolynomialGraphCentreHeredity.graphIdeal (localGraph c) =
      Ideal.map (chartPolynomialMap (ι := ι) A c) globalCentre
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
