import PCRLean.Experimental.FiniteSpanningSetSurjectionAtomic
import PCRLean.Experimental.ProjectiveSurjectionSplitAtomic

/-!
# Finite spanning projective modules admit split finite-free presentations

This file composes the finite-spanning-set surjection with projective lifting.
It gives the exact split-presentation certificate needed by the X032 order-ideal
compiler whenever a finite spanning set has been constructed.
-/

namespace PCRLean
namespace Experimental
namespace FiniteProjectiveSplitPresentationAtomic

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable [Module.Projective R P]

open FiniteSpanningSetSurjectionAtomic
open ProjectiveSurjectionSplitAtomic

/-- Explicit finite-free retraction certificate. -/
structure SplitFreePresentation (s : Finset P) where
  project : (s → R) →ₗ[R] P
  section : P →ₗ[R] (s → R)
  rightInverse : project.comp section = LinearMap.id

/-- A finite spanning set on a projective module yields a split finite-free
presentation. -/
noncomputable def ofSpanningSet
    (s : Finset P) (hspan : Submodule.span R (s : Set P) = ⊤) :
    SplitFreePresentation (R := R) s := by
  let q : (s → R) →ₗ[R] P := generatorMap (R := R) s
  have hq : Function.Surjective q :=
    generatorMap_surjective (R := R) s hspan
  let section : P →ₗ[R] (s → R) :=
    Classical.choose (projective_surjection_splits q hq)
  have hsection : q.comp section = LinearMap.id :=
    Classical.choose_spec (projective_surjection_splits q hq)
  exact {
    project := q
    section := section
    rightInverse := hsection
  }

/-- Existence form of the split-presentation certificate. -/
theorem exists_splitFreePresentation
    (s : Finset P) (hspan : Submodule.span R (s : Set P) = ⊤) :
    Nonempty (SplitFreePresentation (R := R) s) :=
  ⟨ofSpanningSet (R := R) s hspan⟩

end

end FiniteProjectiveSplitPresentationAtomic
end Experimental
end PCRLean
