import Mathlib
import Mathlib.AlgebraicGeometry.StructureSheaf
import PCRLean.Experimental.FittingGraphCentreAtlas
import PCRLean.Experimental.FittingGraphCechEffectivity

/-!
# From localization graph data to an actual global graph

Sections of the affine structure sheaf on `D(d_c)` and the canonical away
localization `R_{d_c}` are two localizations of `R` at the same submonoid.
Hence they are canonically equivalent as `R`-algebras.

This file transports graph tuples in the localization charts to structure-sheaf
sections.  If those sections are pairwise compatible, the sheaf condition and
the global-sections equivalence produce an actual tuple `h : ι → R`.  The
original graph tuple on every determinant chart is then proved to be exactly
the image of `h` in the canonical away localization.

Thus the only remaining affine gluing interface is to derive structure-sheaf
compatibility from the already available double-localization compatibility.
No existence or choice of a global coefficient remains after that bridge.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphSectionAtlas

noncomputable section

open CategoryTheory
open TopCat
open TopologicalSpace
open TopologicalSpace.Opens
open Opposite

universe u v w

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w}

open FittingGraphCentreAtlas
open FittingGraphCechEffectivity

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}

/-- Structure-sheaf section ring on one determinant basic open. -/
abbrev SectionRing (c : Chart) :=
  ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
    (op (chartOpen A c)))

/-- Canonical equivalence between the chosen away localization and the
structure-sheaf sections on the same basic open. -/
noncomputable def chartSectionEquiv (c : Chart) :
    ChartRing A c ≃ₐ[R] SectionRing (A := A) c :=
  IsLocalization.algEquiv
    (Submonoid.powers (A.determinant c))
    (ChartRing A c) (SectionRing (A := A) c)

@[simp] theorem chartSectionEquiv_algebraMap
    (c : Chart) (r : R) :
    chartSectionEquiv (A := A) c
        (algebraMap R (ChartRing A c) r) =
      algebraMap R (SectionRing (A := A) c) r := by
  exact (chartSectionEquiv (A := A) c).commutes r

/-- Localization graph data whose images in the structure sheaf form a
compatible family. -/
structure CompatibleSectionData
    (D : GraphAtlasData (ι := ι) A) : Prop where
  compatible : ∀ i : ι,
    TopCat.Presheaf.IsCompatible
      (AlgebraicGeometry.Spec.structureSheaf R).presheaf
      (chartOpen A)
      (fun c => chartSectionEquiv (A := A) c (D.graph c i))

namespace CompatibleSectionData

variable {D : GraphAtlasData (ι := ι) A}
    (H : CompatibleSectionData D)

/-- Associated structure-sheaf graph atlas. -/
noncomputable def toSectionAtlas :
    FittingGraphCechEffectivity.SectionAtlas (ι := ι) A where
  local := fun c i => chartSectionEquiv (A := A) c (D.graph c i)
  compatible := H.compatible

/-- The actual global graph tuple. -/
noncomputable def globalGraph : ι → R :=
  H.toSectionAtlas.globalGraph

/-- Restricting an actual global coefficient to a basic open is the local
algebra map. -/
theorem restrict_globalCoefficient_eq_algebraMap
    (c : Chart) (r : R) :
    (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
        (homOfLE le_top).op
        ((ConcreteCategory.hom
          (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).hom) r) =
      algebraMap R (SectionRing (A := A) c) r := by
  have h := AlgebraicGeometry.StructureSheaf.algebraMap_self_map
    R (op (chartOpen A c)) (op (⊤ : Opens (PrimeSpectrum R)))
      (homOfLE le_top).op
  have h' := congrArg
    (fun f => ConcreteCategory.hom f r) h
  simpa [AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom]
    using h'

/-- The global tuple restricts to every local structure-sheaf graph section. -/
theorem globalGraph_section_restricts
    (c : Chart) (i : ι) :
    algebraMap R (SectionRing (A := A) c) (H.globalGraph i) =
      chartSectionEquiv (A := A) c (D.graph c i) := by
  rw [← H.restrict_globalCoefficient_eq_algebraMap c (H.globalGraph i)]
  exact H.toSectionAtlas.globalGraph_restricts c i

/-- Main effectivity theorem: every original localization graph coefficient is
exactly the localization of the actual global coefficient. -/
theorem globalGraph_localizes
    (c : Chart) (i : ι) :
    algebraMap R (ChartRing A c) (H.globalGraph i) =
      D.graph c i := by
  apply (chartSectionEquiv (A := A) c).injective
  rw [chartSectionEquiv_algebraMap]
  exact H.globalGraph_section_restricts c i

/-- The local graph centre is exactly the base change of the global graph
centre on every determinant chart. -/
theorem local_graphIdeal_eq_global_baseChange
    [IsDomain R]
    (c : Chart) :
    PolynomialGraphCentreHeredity.graphIdeal (D.graph c) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal H.globalGraph) := by
  symm
  apply PolynomialGraphBaseChange.map_graphIdeal_eq_of_pointwise
  intro i
  exact H.globalGraph_localizes c i

/-- Affine effectivity certificate. -/
structure Certificate where
  globalGraph : ι → R
  localizes : ∀ c i,
    algebraMap R (ChartRing A c) (globalGraph i) = D.graph c i
  centreBaseChange : ∀ c,
    PolynomialGraphCentreHeredity.graphIdeal (D.graph c) =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι) (algebraMap R (ChartRing A c)))
        (PolynomialGraphCentreHeredity.graphIdeal globalGraph)

/-- Assemble the actual global graph and centre. -/
noncomputable def certificate [IsDomain R] : Certificate H where
  globalGraph := H.globalGraph
  localizes := H.globalGraph_localizes
  centreBaseChange := H.local_graphIdeal_eq_global_baseChange

end CompatibleSectionData

end

end FittingGraphSectionAtlas
end Experimental
end PCRLean
