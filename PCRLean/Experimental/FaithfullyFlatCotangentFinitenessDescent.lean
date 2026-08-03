import Mathlib
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.CotangentBaseChange

/-!
# Faithfully flat descent of conormal finiteness

Let `A → B` be faithfully flat and let `I ⊂ A`.  The conormal module
`I/I²` is finite over `A` as soon as its scalar extension

`B ⊗[A] (I/I²)`

is finite over `B`.  This is the exact finiteness component required to descend
an explicit free conormal basis from a faithfully flat coordinate or graph
model.

The theorem does not yet descend projectivity or local freeness.  Those require
an additional flat/projective descent theorem and the identification of the
base-changed cotangent module with the cotangent module of the extended ideal.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatCotangentFinitenessDescent

noncomputable section

universe u v w

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Finiteness of the base-changed conormal module descends faithfully flatly. -/
theorem cotangent_finite_of_tensorProduct
    (I : Ideal A)
    [Module.Finite B (B ⊗[A] I.Cotangent)] :
    Module.Finite A I.Cotangent :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- It is enough to identify the base-changed conormal module with any finite
`B`-module. -/
theorem cotangent_finite_of_baseChange_equiv
    (I : Ideal A)
    {N : Type w} [AddCommMonoid N] [Module B N] [Module.Finite B N]
    (e : B ⊗[A] I.Cotangent ≃ₗ[B] N) :
    Module.Finite A I.Cotangent := by
  letI : Module.Finite B (B ⊗[A] I.Cotangent) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact cotangent_finite_of_tensorProduct (B := B) I

end

end FaithfullyFlatCotangentFinitenessDescent
end Experimental
end PCRLean
