import Mathlib
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.CotangentBaseChange

/-!
# Faithfully flat descent of projective conormal data

A finite locally free conormal module on a faithfully flat chart should descend
to a finite projective conormal module on the base.  The module-theoretic core
splits into two independent descent statements:

* flatness of `B ⊗[A] (I/I²)` descends to flatness of `I/I²`;
* finite presentation of the scalar extension descends to finite presentation
  of `I/I²`.

A finitely presented flat module is projective.  This file attempts to compile
those standard descent facts into one exact theorem for conormal modules.  The
remaining geometric task is to construct the actual base-change equivalence
between `B ⊗[A] (I/I²)` and the conormal module of the extended graph ideal.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatCotangentProjectiveDescent

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Flatness of the base-changed conormal module descends. -/
theorem cotangent_flat_of_tensorProduct
    (I : Ideal A)
    [Module.Flat B (B ⊗[A] I.Cotangent)] :
    Module.Flat A I.Cotangent :=
  Module.Flat.of_flat_tensorProduct_of_faithfullyFlat B

/-- Finite presentation of the base-changed conormal module descends. -/
theorem cotangent_finitePresentation_of_tensorProduct
    (I : Ideal A)
    [Module.FinitePresentation B (B ⊗[A] I.Cotangent)] :
    Module.FinitePresentation A I.Cotangent :=
  Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B

/-- A finite locally free faithfully flat model yields a finite projective
conormal module on the base. -/
theorem cotangent_projective_of_tensorProduct
    (I : Ideal A)
    [Module.Flat B (B ⊗[A] I.Cotangent)]
    [Module.FinitePresentation B (B ⊗[A] I.Cotangent)] :
    Module.Projective A I.Cotangent := by
  letI : Module.Flat A I.Cotangent :=
    cotangent_flat_of_tensorProduct (B := B) I
  letI : Module.FinitePresentation A I.Cotangent :=
    cotangent_finitePresentation_of_tensorProduct (B := B) I
  infer_instance

end

end FaithfullyFlatCotangentProjectiveDescent
end Experimental
end PCRLean
