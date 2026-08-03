import Mathlib
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import PCRLean.Experimental.FittingMinorAtlas
import PCRLean.Experimental.FittingGraphCechEffectivity
import PCRLean.Experimental.FittingGraphSectionAtlas

/-!
# Faithful equality reflection on a finite Fitting cover

A finite determinant family whose basic opens cover `Spec R` is jointly
faithful: two elements of `R` are equal as soon as they have the same image in
every canonical away localization.

The proof is deliberately sheaf-theoretic.  The global sections of the affine
structure sheaf are `R`; the restrictions of the two global sections agree on
every determinant open; and uniqueness of sheaf gluing forces the global
sections, hence the original coefficients, to agree.

This lemma is the affine local-to-global cancellation principle used below to
turn chartwise linear-system equations into one actual global equation.
-/

namespace PCRLean
namespace Experimental
namespace FittingMinorFaithfulCover

noncomputable section

open CategoryTheory
open TopCat
open TopologicalSpace
open TopologicalSpace.Opens
open Opposite

universe u v

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]

open FittingGraphCentreAtlas
open FittingGraphCechEffectivity
open FittingGraphSectionAtlas

variable (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))

/-- Global structure-sheaf section represented by one coefficient of `R`. -/
def globalSection (r : R) :
    ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
      (op (⊤ : Opens (PrimeSpectrum R)))) :=
  (ConcreteCategory.hom
    (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).hom) r

/-- Restriction of an actual global coefficient to a determinant chart is the
usual algebra map into the chart section ring. -/
theorem restrict_globalSection
    (c : Chart) (r : R) :
    (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
        (homOfLE le_top).op (A.globalSection r) =
      algebraMap R (SectionRing (A := A) c) r := by
  have h := AlgebraicGeometry.StructureSheaf.algebraMap_self_map
    R (op (chartOpen A c))
      (op (⊤ : Opens (PrimeSpectrum R)))
      (homOfLE le_top).op
  have h' := congrArg (fun f => ConcreteCategory.hom f r) h
  simpa [globalSection,
    AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom] using h'

/-- The determinant basic opens jointly reflect equality in the base ring. -/
theorem eq_of_chart_algebraMap_eq
    {x y : R}
    (h : ∀ c : Chart,
      algebraMap R (ChartRing A c) x =
        algebraMap R (ChartRing A c) y) :
    x = y := by
  have hcover :
      (⊤ : Opens (PrimeSpectrum R)) ≤
        ⨆ c : Chart, chartOpen A c := by
    rw [show (⨆ c : Chart, chartOpen A c) = ⊤ from A.basicOpen_cover]
  have hsections : A.globalSection x = A.globalSection y := by
    apply (AlgebraicGeometry.Spec.structureSheaf R).eq_of_locally_eq'
      (chartOpen A) (⊤ : Opens (PrimeSpectrum R))
      (fun _ => homOfLE le_top) hcover
    intro c
    rw [A.restrict_globalSection c x,
      A.restrict_globalSection c y]
    have hc := congrArg (chartSectionEquiv (A := A) c) (h c)
    simpa using hc
  have hback := congrArg
    (ConcreteCategory.hom
      (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).inv)
    hsections
  simpa [globalSection] using hback

/-- Vanishing in every determinant localization implies actual vanishing. -/
theorem eq_zero_of_chart_algebraMap_eq_zero
    {x : R}
    (h : ∀ c : Chart,
      algebraMap R (ChartRing A c) x = 0) :
    x = 0 := by
  apply A.eq_of_chart_algebraMap_eq
  intro c
  simpa using h c

/-- Equality of finite tuples is reflected coordinatewise by the determinant
cover. -/
theorem funext_of_chart_algebraMap_eq
    {ι : Type*} {x y : ι → R}
    (h : ∀ c : Chart, ∀ i : ι,
      algebraMap R (ChartRing A c) (x i) =
        algebraMap R (ChartRing A c) (y i)) :
    x = y := by
  funext i
  exact A.eq_of_chart_algebraMap_eq (fun c => h c i)

end

end FittingMinorFaithfulCover
end Experimental
end PCRLean
