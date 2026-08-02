import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness certificates for the restricted passive packets

The explicit PCR chambers declare passive objects to be finite locally free
modules pulled back from the smooth base.  At the affine algebra level, free
modules are flat, and hence tensoring with them preserves injective maps.  This
file records that exact homological certificate.  It does not prove that an
arbitrary passive owner is locally free, nor that normal flatness holds for an
arbitrary geometric centre.
-/

namespace PCRLean.Algebra.PassiveFlatness

variable {R : Type*} [CommSemiring R]
variable {M N P : Type*}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- A free passive module is flat. -/
theorem flat_of_free [Module.Free R M] : Module.Flat R M := by
  infer_instance

/-- A projective passive module is flat. -/
theorem flat_of_projective [Module.Projective R M] : Module.Flat R M := by
  infer_instance

/-- Tensoring an injective map with a flat passive module remains injective. -/
theorem rTensor_injective [Module.Flat R M]
    (f : N →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (f.rTensor M) :=
  Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- In particular the same conclusion holds for a free passive module. -/
theorem rTensor_injective_of_free [Module.Free R M]
    (f : N →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (f.rTensor M) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

end PCRLean.Algebra.PassiveFlatness
