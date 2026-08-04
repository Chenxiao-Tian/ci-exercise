import Mathlib
import PCRLean.Experimental.FiniteProjectiveAutomaticDualFrame
import PCRLean.Experimental.CokernelOrderIdealCompiler

/-!
# Automatic order-ideal trichotomy for finite projective cokernels

The X031 compiler previously required a finite dual frame as an explicit input.
For a cokernel that is both finite and projective, the preceding atomic theorem
constructs a finite dual frame automatically.  This file packages the resulting
finite index, frame, and graph/proper-hybrid/unit status in one certificate.

The theorem is purely algebraic.  The unresolved geometric edge is to prove
that the cokernel naturally attached to every relevant resolution state is
finite projective on a finite compatible atlas, and to transport these
certificates through charts and overlaps without reset.
-/

namespace PCRLean
namespace Experimental
namespace FiniteProjectiveCokernelOrderIdealCompiler

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {N : Type v} {E : Type w}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

open DeterminantalCokernelObstruction
open FiniteProjectiveAutomaticDualFrame

abbrev Q (φ : N →ₗ[R] E) := E ⧸ LinearMap.range φ

/-- A first-class automatically generated X031 status package. -/
structure AutomaticStatus
    (φ : N →ₗ[R] E) (b : E)
    [Module.Finite R (Q φ)] [Module.Projective R (Q φ)] where
  n : ℕ
  frame : ProjectiveMoritaDescent.DualFrame
    (R := R) (P := Q φ) (ι := Fin n)
  status : CokernelOrderIdealCompiler.Status φ b frame

/-- Every finite projective cokernel obstruction has a fully typed finite-frame
order-ideal status. -/
noncomputable def compile
    (φ : N →ₗ[R] E) (b : E)
    [Module.Finite R (Q φ)] [Module.Projective R (Q φ)] :
    AutomaticStatus φ b := by
  let C := automaticFrameCertificate (R := R) (P := Q φ)
  exact
    { n := C.n
      frame := C.frame
      status := CokernelOrderIdealCompiler.compile φ b C.frame }

/-- Exact branch coverage independently of the chosen automatically constructed
frame. -/
theorem branch_coverage
    (φ : N →ₗ[R] E) (b : E) :
    CokernelOrderIdeal.obstructionIdeal φ b = ⊥ ∨
      (CokernelOrderIdeal.obstructionIdeal φ b ≠ ⊥ ∧
        CokernelOrderIdeal.obstructionIdeal φ b ≠ ⊤) ∨
      CokernelOrderIdeal.obstructionIdeal φ b = ⊤ := by
  classical
  by_cases hbot : CokernelOrderIdeal.obstructionIdeal φ b = ⊥
  · exact Or.inl hbot
  · by_cases htop : CokernelOrderIdeal.obstructionIdeal φ b = ⊤
    · exact Or.inr (Or.inr htop)
    · exact Or.inr (Or.inl ⟨hbot, htop⟩)

/-- The automatically constructed certificate supplies an inhabitant of the
existing X031 status type. -/
theorem automatic_status_nonempty
    (φ : N →ₗ[R] E) (b : E)
    [Module.Finite R (Q φ)] [Module.Projective R (Q φ)] :
    Nonempty (AutomaticStatus φ b) :=
  ⟨compile φ b⟩

end

end FiniteProjectiveCokernelOrderIdealCompiler
end Experimental
end PCRLean
