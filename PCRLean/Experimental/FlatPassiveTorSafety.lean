import Mathlib.RingTheory.Flat.Basic

/-!
# Flat passive modules are Tor-safe along every centre

For an ideal `I ⊂ A` and a passive `A`-module `M`, the first concrete Tor gate
is injectivity of

`I ⊗ M → A ⊗ M`

induced by the ideal inclusion.  If `M` is flat, tensoring preserves every
injective linear map, so this gate holds for every centre ideal, independently
of its equations.

This closes the passive-safety chamber for flat modules, including free and
projective passive data.  It does not prove normal flatness for arbitrary
nonflat modules, nor does it identify the associated graded module along the
centre.
-/

namespace PCRLean
namespace Experimental
namespace FlatPassiveTorSafety

noncomputable section

universe u v

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- Concrete first-Tor safety gate for a passive module along one centre. -/
def TorSafe (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] : Prop :=
  Function.Injective (I.subtype.rTensor M)

/-- A flat passive module is Tor-safe along every centre ideal. -/
theorem torSafe_of_flat [Module.Flat A M] (I : Ideal A) :
    TorSafe I M := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    I.subtype Subtype.val_injective

/-- Free passive modules are Tor-safe. -/
theorem torSafe_of_free [Module.Free A M] (I : Ideal A) :
    TorSafe I M := by
  letI : Module.Flat A M := Module.Flat.of_free
  exact torSafe_of_flat I

/-- Projective passive modules are Tor-safe. -/
theorem torSafe_of_projective [Module.Projective A M] (I : Ideal A) :
    TorSafe I M := by
  letI : Module.Flat A M := Module.Flat.of_projective
  exact torSafe_of_flat I

/-- One flatness hypothesis certifies passive safety simultaneously for every
centre in a family. -/
theorem torSafe_family_of_flat
    [Module.Flat A M]
    {Centre : Type*} (I : Centre → Ideal A) :
    ∀ c : Centre, TorSafe (I c) M := by
  intro c
  exact torSafe_of_flat (I c)

/-- A family of flat passive owners is simultaneously safe along one centre. -/
theorem owners_torSafe_of_flat
    {Owner : Type*}
    (P : Owner → Type v)
    [∀ o, AddCommGroup (P o)]
    [∀ o, Module A (P o)]
    [∀ o, Module.Flat A (P o)]
    (I : Ideal A) :
    ∀ o : Owner, TorSafe I (P o) := by
  intro o
  exact torSafe_of_flat I

end

end FlatPassiveTorSafety
end Experimental
end PCRLean
