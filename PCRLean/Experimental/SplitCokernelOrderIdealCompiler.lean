import Mathlib
import PCRLean.Experimental.FiniteProjectivePresentationDualFrame
import PCRLean.Experimental.CokernelOrderIdealCompiler

/-!
# Cokernel order-ideal compiler from a split finite-free presentation

This file removes the independent dual-frame input from the X031 cokernel
trichotomy. A split finite-free presentation of the finite-projective cokernel
canonically supplies the required finite dual frame, after which the existing
graph / proper-hybrid / unit-obstruction compiler applies.
-/

namespace PCRLean
namespace Experimental
namespace SplitCokernelOrderIdealCompiler

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {N : Type v} {E : Type w}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

open FiniteProjectivePresentationDualFrame
open DeterminantalCokernelObstruction

abbrev Q (φ : N →ₗ[R] E) := E ⧸ LinearMap.range φ

/-- Existing trichotomy specialized to the frame produced by a split finite
free presentation. -/
abbrev Status
    (φ : N →ₗ[R] E) (b : E)
    (F : SplitFiniteFreePresentation (R := R) (P := Q φ) (ι := ι)) :=
  CokernelOrderIdealCompiler.Status φ b F.toDualFrame

/-- Compile the exact trichotomy without a separately supplied dual frame. -/
noncomputable def compile
    (φ : N →ₗ[R] E) (b : E)
    (F : SplitFiniteFreePresentation (R := R) (P := Q φ) (ι := ι)) :
    Status φ b F :=
  CokernelOrderIdealCompiler.compile φ b F.toDualFrame

/-- Pure logical coverage of the three order-ideal states. -/
theorem status_coverage
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

/-- A projective cokernel plus any surjective finite-free presentation yields a
fully typed trichotomy certificate. -/
noncomputable def compileOfProjectivePresentation
    [Module.Projective R (Q φ)]
    (φ : N →ₗ[R] E) (b : E)
    (project : (ι → R) →ₗ[R] Q φ)
    (hproject : Function.Surjective project) :
    Status φ b
      (FiniteProjectivePresentationDualFrame.ofProjectiveSurjection
        project hproject) :=
  compile φ b
    (FiniteProjectivePresentationDualFrame.ofProjectiveSurjection
      project hproject)

/-- Edge-soundness theorem: the automatically produced object is exactly an
instance of the established X031 trichotomy. -/
theorem splitPresentation_edge_sound
    [Module.Projective R (Q φ)]
    (φ : N →ₗ[R] E) (b : E)
    (project : (ι → R) →ₗ[R] Q φ)
    (hproject : Function.Surjective project) :
    Nonempty
      (CokernelOrderIdealCompiler.Status φ b
        (FiniteProjectivePresentationDualFrame.dualFrameOfProjectiveSurjection
          project hproject)) := by
  exact ⟨compileOfProjectivePresentation φ b project hproject⟩

end

end SplitCokernelOrderIdealCompiler
end Experimental
end PCRLean
