import Mathlib
import Mathlib.AlgebraicGeometry.StructureSheaf
import PCRLean.Experimental.FittingGraphCentreOverlap
import PCRLean.Experimental.FittingGraphSectionAtlas

/-!
# Localization overlap compatibility implies sheaf compatibility

The determinant chart ring `R_{d_c}` is canonically equivalent to the
structure-sheaf sections on `D(d_c)`.  Likewise, the double localization
`R_{d_c d_d}` is canonically equivalent to the sections on

`D(d_c) ∩ D(d_d) = D(d_c d_d)`.

This file proves that, under those equivalences, the canonical localization
maps to `R_{d_c d_d}` are exactly the structure-sheaf restriction maps.
The proof uses the uniqueness property of localization homomorphisms: both
maps agree on the base ring `R`.

Consequently, pointwise compatibility of local graph tuples in the explicit
double localizations implies compatibility as structure-sheaf sections.  The
Čech-effectivity compiler then produces one actual global graph tuple and one
global graph ideal whose extension equals every local centre ideal.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphRestrictionCompatibility

noncomputable section

open CategoryTheory
open TopCat
open TopologicalSpace
open TopologicalSpace.Opens
open Opposite

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open FittingGraphCentreAtlas
open FittingGraphCentreOverlap
open FittingGraphCechEffectivity
open FittingGraphSectionAtlas

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}

/-- Intersection of two determinant basic opens. -/
def overlapOpen (c d : Chart) : Opens (PrimeSpectrum R) :=
  chartOpen A c ⊓ chartOpen A d

/-- Structure-sheaf section ring on one overlap. -/
abbrev OverlapSectionRing (c d : Chart) :=
  ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
    (op (overlapOpen (A := A) c d)))

/-- The intersection open is the basic open of the product determinant. -/
theorem overlapOpen_eq_basicOpen_mul (c d : Chart) :
    overlapOpen (A := A) c d =
      PrimeSpectrum.basicOpen (A.determinant c * A.determinant d) := by
  symm
  exact PrimeSpectrum.basicOpen_mul
    (A.determinant c) (A.determinant d)

/-- The overlap section ring is itself the expected away localization. -/
noncomputable instance overlapSection_isLocalizationAway (c d : Chart) :
    IsLocalization.Away
      (A.determinant c * A.determinant d)
      (OverlapSectionRing (A := A) c d) := by
  rw [overlapOpen_eq_basicOpen_mul (A := A) c d]
  infer_instance

/-- Canonical equivalence between the explicit double localization and the
structure-sheaf overlap sections. -/
noncomputable def overlapSectionEquiv (c d : Chart) :
    OverlapRing (A := A) c d ≃ₐ[R]
      OverlapSectionRing (A := A) c d :=
  IsLocalization.algEquiv
    (Submonoid.powers (A.determinant c * A.determinant d))
    (OverlapRing (A := A) c d)
    (OverlapSectionRing (A := A) c d)

/-- Structure-sheaf restriction from the first chart to the intersection. -/
def restrictionLeft (c d : Chart) :
    SectionRing (A := A) c →+*
      OverlapSectionRing (A := A) c d :=
  ConcreteCategory.hom
    ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
      (infLELeft (chartOpen A c) (chartOpen A d)).op)

/-- Structure-sheaf restriction from the second chart to the intersection. -/
def restrictionRight (c d : Chart) :
    SectionRing (A := A) d →+*
      OverlapSectionRing (A := A) c d :=
  ConcreteCategory.hom
    ((AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
      (infLERight (chartOpen A c) (chartOpen A d)).op)

@[simp] theorem restrictionLeft_algebraMap
    (c d : Chart) (r : R) :
    restrictionLeft (A := A) c d
        (algebraMap R (SectionRing (A := A) c) r) =
      algebraMap R (OverlapSectionRing (A := A) c d) r := by
  have h := AlgebraicGeometry.StructureSheaf.algebraMap_self_map
    R (op (overlapOpen (A := A) c d)) (op (chartOpen A c))
      (infLELeft (chartOpen A c) (chartOpen A d)).op
  have h' := congrArg (fun f => ConcreteCategory.hom f r) h
  simpa [restrictionLeft, overlapOpen] using h'

@[simp] theorem restrictionRight_algebraMap
    (c d : Chart) (r : R) :
    restrictionRight (A := A) c d
        (algebraMap R (SectionRing (A := A) d) r) =
      algebraMap R (OverlapSectionRing (A := A) c d) r := by
  have h := AlgebraicGeometry.StructureSheaf.algebraMap_self_map
    R (op (overlapOpen (A := A) c d)) (op (chartOpen A d))
      (infLERight (chartOpen A c) (chartOpen A d)).op
  have h' := congrArg (fun f => ConcreteCategory.hom f r) h
  simpa [restrictionRight, overlapOpen] using h'

/-- The explicit left localization map is the first structure-sheaf
restriction under the canonical equivalences. -/
theorem overlapSectionEquiv_comp_leftMap (c d : Chart) :
    (overlapSectionEquiv (A := A) c d).toRingHom.comp
        (leftMap (A := A) c d) =
      (restrictionLeft (A := A) c d).comp
        (chartSectionEquiv (A := A) c).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (A.determinant c))
  ext r
  simp

/-- The explicit right localization map is the second structure-sheaf
restriction under the canonical equivalences. -/
theorem overlapSectionEquiv_comp_rightMap (c d : Chart) :
    (overlapSectionEquiv (A := A) c d).toRingHom.comp
        (rightMap (A := A) c d) =
      (restrictionRight (A := A) c d).comp
        (chartSectionEquiv (A := A) d).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (A.determinant d))
  ext r
  simp

/-- Pointwise form of the left comparison. -/
theorem overlapSectionEquiv_leftMap_apply
    (c d : Chart) (x : ChartRing A c) :
    overlapSectionEquiv (A := A) c d
        (leftMap (A := A) c d x) =
      restrictionLeft (A := A) c d
        (chartSectionEquiv (A := A) c x) := by
  have h := congrArg (fun f => f x)
    (overlapSectionEquiv_comp_leftMap (A := A) c d)
  exact h

/-- Pointwise form of the right comparison. -/
theorem overlapSectionEquiv_rightMap_apply
    (c d : Chart) (x : ChartRing A d) :
    overlapSectionEquiv (A := A) c d
        (rightMap (A := A) c d x) =
      restrictionRight (A := A) c d
        (chartSectionEquiv (A := A) d x) := by
  have h := congrArg (fun f => f x)
    (overlapSectionEquiv_comp_rightMap (A := A) c d)
  exact h

namespace FittingGraphCentreOverlap.Compatible

variable {D : GraphAtlasData (ι := ι) A}
    (H : FittingGraphCentreOverlap.Compatible D)

/-- Double-localization compatibility automatically gives structure-sheaf
compatibility. -/
noncomputable def toCompatibleSectionData :
    FittingGraphSectionAtlas.CompatibleSectionData D where
  compatible := by
    intro i c d
    have h := congrArg
      (overlapSectionEquiv (A := A) c d)
      (H.graph_eq c d i)
    simpa [restrictionLeft, restrictionRight] using
      (H.overlapSectionEquiv_leftMap_apply c d (D.graph c i)).symm.trans
        (h.trans (H.overlapSectionEquiv_rightMap_apply
          c d (D.graph d i)))

/-- Main affine-globalization theorem: compatible local graph data on a finite
Fitting cover comes from one actual global graph tuple and one global centre
ideal. -/
noncomputable def globalizationCertificate :
    FittingGraphSectionAtlas.CompatibleSectionData.Certificate
      H.toCompatibleSectionData :=
  H.toCompatibleSectionData.certificate

/-- Every local graph coefficient is the localization of the global one. -/
theorem globalGraph_localizes (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c)
        (H.toCompatibleSectionData.globalGraph i) =
      D.graph c i :=
  H.toCompatibleSectionData.globalGraph_localizes c i

/-- Every local centre ideal is exactly the base change of one global actual
centre ideal. -/
theorem local_centre_is_global_baseChange (c : Chart) :
    PolynomialGraphCentreHeredity.graphIdeal (D.graph c) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal
          H.toCompatibleSectionData.globalGraph) :=
  H.toCompatibleSectionData.local_graphIdeal_eq_global_baseChange c

end FittingGraphCentreOverlap.Compatible

end

end FittingGraphRestrictionCompatibility
end Experimental
end PCRLean
