import Mathlib.RingTheory.Flat.Basic

/-!
# Free passive owner safety

Free passive modules are flat. Hence tensoring with them preserves injections,
and all higher Tor groups against them vanish. This is the exact passive-safety
subchamber used by MLEL-002.
-/

namespace PCRLean
namespace FreePassiveOwnerSafety

noncomputable section

universe u v w x

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- A free passive module is flat. -/
theorem flat_of_free [Module.Free A M] : Module.Flat A M := by
  infer_instance

/-- Tensoring an injection with a free passive module preserves injectivity. -/
theorem rTensor_preserves_injective
    [Module.Free A M]
    {N : Type w} {P : Type x}
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (f : N →ₗ[A] P) (hf : Function.Injective f) :
    Function.Injective (f.rTensor M) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- Left-tensor form of the same passive-safety gate. -/
theorem lTensor_preserves_injective
    [Module.Free A M]
    {N : Type w} {P : Type x}
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (f : N →ₗ[A] P) (hf : Function.Injective f) :
    Function.Injective (f.lTensor M) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

end

end FreePassiveOwnerSafety
end PCRLean
