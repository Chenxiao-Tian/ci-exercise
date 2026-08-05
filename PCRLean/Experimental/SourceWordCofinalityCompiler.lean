import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Source-word cofinality compiler

A centre-exact source word ends with a flat strict transform.  Standard strict-
transform transitivity and flat pullback are expected to identify its transform
on any certified common refinement with the pullback of that flat terminal
module.  Once the scheme theorem supplies a linear equivalence for each source,
flatness of the full finite source portfolio is formal.

This file proves only that abstract backend.  It does not prove that a word can
be represented by a centre-exact composite blowup ideal, that a product blowup
is a common refinement in the required scheme category, or that iterated strict
transforms agree with the displayed pullbacks.
-/

namespace PCRLean
namespace Experimental
namespace SourceWordCofinalityCompiler

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {Source : Type w} [Fintype Source] [DecidableEq Source]
variable (Terminal Common : Source → Type v)
variable [∀ s, AddCommGroup (Terminal s)]
variable [∀ s, Module A (Terminal s)]
variable [∀ s, AddCommGroup (Common s)]
variable [∀ s, Module A (Common s)]

/-- Exact source-by-source comparison delivered by a centre-exact common-
refinement theorem. -/
structure Certificate where
  equiv : ∀ s, Common s ≃ₗ[A] Terminal s

namespace Certificate

/-- A flat terminal source transform stays flat on the common refinement. -/
theorem commonFlat
    (C : Certificate (A := A) Terminal Common)
    (hTerminal : ∀ s, Module.Flat A (Terminal s))
    (s : Source) :
    Module.Flat A (Common s) := by
  letI : Module.Flat A (Terminal s) := hTerminal s
  exact Module.Flat.of_linearEquiv (C.equiv s)

/-- The complete finite common-refinement source portfolio is flat. -/
theorem portfolioFlat
    (C : Certificate (A := A) Terminal Common)
    (hTerminal : ∀ s, Module.Flat A (Terminal s)) :
    Module.Flat A (DirectSum Source Common) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro s
  exact commonFlat Terminal Common C hTerminal s

end Certificate

end

end SourceWordCofinalityCompiler
end Experimental
end PCRLean
