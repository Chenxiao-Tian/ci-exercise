import Mathlib
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import PCRLean.Experimental.FittingMinorAtlas

/-!
# Čech effectivity for Fitting graph sections

The structure sheaf on `Spec R` is a sheaf, its sections on `D(d)` are the away
localization `R_d`, and its global sections are canonically `R`.

For a finite determinant cover, this module packages graph coefficients as
sections on the determinant basic opens.  Pairwise compatibility on
intersections produces a unique global section by the sheaf condition.  The
global-sections equivalence then produces an actual coefficient in `R` whose
restriction is every local graph coefficient.

This is the affine Čech-effectivity theorem needed after pairwise overlap
compatibility.  A later compiler identifies the local localization elements
with these structure-sheaf sections and uses the resulting global tuple to
define one actual global graph ideal.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphCechEffectivity

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

/-- Determinant basic open. -/
def chartOpen
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (c : Chart) : Opens (PrimeSpectrum R) :=
  PrimeSpectrum.basicOpen (A.determinant c)

/-- One compatible family of graph coefficients in the affine structure sheaf. -/
structure SectionAtlas
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)) where
  local : ∀ c : Chart, ι →
    ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
      (op (chartOpen A c)))
  compatible : ∀ i : ι,
    TopCat.Presheaf.IsCompatible
      (AlgebraicGeometry.Spec.structureSheaf R).presheaf
      (chartOpen A)
      (fun c => local c i)

namespace SectionAtlas

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
    (D : SectionAtlas (ι := ι) A)

/-- The determinant opens cover the terminal open. -/
theorem top_le_iSup_chartOpen :
    (⊤ : Opens (PrimeSpectrum R)) ≤ ⨆ c : Chart, chartOpen A c := by
  rw [show (⨆ c : Chart, chartOpen A c) = ⊤ from A.basicOpen_cover]

/-- Existence of one global structure-sheaf section gluing a chosen graph
coefficient. -/
theorem exists_gluedSection (i : ι) :
    ∃ s : ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj (op ⊤)),
      ∀ c : Chart,
        (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
            (homOfLE le_top).op s = D.local c i := by
  obtain ⟨s, hs, -⟩ :=
    (AlgebraicGeometry.Spec.structureSheaf R).existsUnique_gluing'
      (chartOpen A) ⊤ (fun _ => homOfLE le_top)
      D.top_le_iSup_chartOpen
      (fun c => D.local c i) (D.compatible i)
  exact ⟨s, hs⟩

/-- Chosen global section. -/
noncomputable def gluedSection (i : ι) :
    ↑((AlgebraicGeometry.Spec.structureSheaf R).obj.obj (op ⊤)) :=
  Classical.choose (D.exists_gluedSection i)

/-- The chosen global section has the required restrictions. -/
theorem gluedSection_spec (i : ι) (c : Chart) :
    (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
        (homOfLE le_top).op (D.gluedSection i) = D.local c i :=
  (Classical.choose_spec (D.exists_gluedSection i)) c

/-- The actual global coefficient represented by the glued global section. -/
noncomputable def globalCoefficient (i : ι) : R :=
  (ConcreteCategory.hom
    (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).inv)
    (D.gluedSection i)

/-- The global coefficient maps back to the chosen global section. -/
theorem globalCoefficient_toSection (i : ι) :
    (ConcreteCategory.hom
      (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).hom)
      (D.globalCoefficient i) = D.gluedSection i := by
  simp [globalCoefficient]

/-- Every local graph coefficient is the restriction of one actual coefficient
of `R`. -/
theorem globalCoefficient_restricts (i : ι) (c : Chart) :
    (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
        (homOfLE le_top).op
        ((ConcreteCategory.hom
          (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).hom)
          (D.globalCoefficient i)) = D.local c i := by
  rw [D.globalCoefficient_toSection i]
  exact D.gluedSection_spec i c

/-- All graph coordinates glue simultaneously to one global tuple. -/
noncomputable def globalGraph : ι → R :=
  D.globalCoefficient

/-- Simultaneous restriction theorem. -/
theorem globalGraph_restricts (c : Chart) (i : ι) :
    (AlgebraicGeometry.Spec.structureSheaf R).presheaf.map
        (homOfLE le_top).op
        ((ConcreteCategory.hom
          (AlgebraicGeometry.StructureSheaf.globalSectionsIso R).hom)
          (D.globalGraph i)) = D.local c i :=
  D.globalCoefficient_restricts i c

end SectionAtlas

end

end FittingGraphCechEffectivity
end Experimental
end PCRLean
