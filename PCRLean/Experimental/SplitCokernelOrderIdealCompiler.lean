import Mathlib
import PCRLean.Experimental.CokernelOrderIdeal
import PCRLean.Experimental.IntrinsicOrderIdealMinimality
import PCRLean.Experimental.SplitFreePresentationDualFrame

/-!
# Frame-independent split cokernel order-ideal compiler

For `φ : N →ₗ[R] E` and `b : E`, the obstruction is the class

`ω = [b] ∈ E ⧸ range φ`.

A split finite-free presentation of the cokernel supplies dual separation, but
the output status below is formulated intrinsically and does not mention the
chosen frame.  The three branches are:

* graph: the order ideal is zero and `b` is in the range of `φ`;
* hybrid: the order ideal is proper nonzero, absorbs the obstruction, and is
  intrinsically minimal;
* unit obstruction: the order ideal is the unit ideal, so no proper coefficient
  ideal absorbs all dual obstruction values.

This closes the semantic edge from a split finite-free cokernel presentation to
the X031 order-ideal trichotomy.  It does not construct such a presentation for
an arbitrary resolution state and it does not prove regularity or joint
legality of the resulting marked closure.
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

open DeterminantalCokernelObstruction
open ProjectiveSectionOrderIdeal
open IntrinsicOrderIdealMinimality
open SplitFreePresentationDualFrame

abbrev Q (φ : N →ₗ[R] E) := E ⧸ LinearMap.range φ

/-- Intrinsic branch certificate.  Its type is independent of a chosen frame or
split presentation. -/
inductive Status (φ : N →ₗ[R] E) (b : E) : Type (max u v w) where
  | graph
      (ideal_eq_bot : CokernelOrderIdeal.obstructionIdeal φ b = ⊥)
      (solution : ∃ n : N, φ n = b)
  | hybrid
      (ideal_ne_bot : CokernelOrderIdeal.obstructionIdeal φ b ≠ ⊥)
      (ideal_ne_top : CokernelOrderIdeal.obstructionIdeal φ b ≠ ⊤)
      (obstruction_mem :
        obstruction φ b ∈
          CokernelOrderIdeal.obstructionIdeal φ b •
            (⊤ : Submodule R (Q φ)))
      (minimal :
        IsLeast
          {J : Ideal R |
            FunctionalsVanishMod (obstruction φ b) J}
          (CokernelOrderIdeal.obstructionIdeal φ b))
  | unitObstruction
      (ideal_eq_top : CokernelOrderIdeal.obstructionIdeal φ b = ⊤)
      (noProperAbsorption :
        ¬ ∃ J : Ideal R,
          J ≠ ⊤ ∧ FunctionalsVanishMod (obstruction φ b) J)

/-- Exact three-way coverage of an ideal by zero, proper nonzero, and unit
status. -/
theorem ideal_trichotomy
    (J : Ideal R) :
    J = ⊥ ∨ (J ≠ ⊥ ∧ J ≠ ⊤) ∨ J = ⊤ := by
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  · by_cases htop : J = ⊤
    · exact Or.inr (Or.inr htop)
    · exact Or.inr (Or.inl ⟨hbot, htop⟩)

/-- A split presentation of the cokernel makes zero order ideal equivalent to
exact effectivity of the affine equation. -/
theorem obstructionIdeal_eq_bot_iff_exists
    (φ : N →ₗ[R] E) (b : E)
    (S : SplitFreePresentation (R := R) (P := Q φ) (ι := ι)) :
    CokernelOrderIdeal.obstructionIdeal φ b = ⊥ ↔
      ∃ n : N, φ n = b :=
  CokernelOrderIdeal.obstructionIdeal_eq_bot_iff_exists φ b S.dualFrame

/-- Compile the frame-independent intrinsic status from a split finite-free
presentation of the cokernel. -/
noncomputable def compile
    (φ : N →ₗ[R] E) (b : E)
    (S : SplitFreePresentation (R := R) (P := Q φ) (ι := ι)) :
    Status φ b := by
  classical
  by_cases hbot : CokernelOrderIdeal.obstructionIdeal φ b = ⊥
  · exact Status.graph hbot
      ((obstructionIdeal_eq_bot_iff_exists φ b S).mp hbot)
  · by_cases htop : CokernelOrderIdeal.obstructionIdeal φ b = ⊤
    · exact Status.unitObstruction htop
        (no_proper_ideal_absorbs_unit_intrinsic
          (obstruction φ b) htop)
    · exact Status.hybrid hbot htop
        (CokernelOrderIdeal.obstruction_mem_orderIdeal_smul_top
          φ b S.dualFrame)
        (orderIdeal_isLeast_intrinsic (obstruction φ b))

/-- The graph branch condition is independent of which split presentation is
used. -/
theorem graphCondition_independent
    (φ : N →ₗ[R] E) (b : E)
    (S T : SplitFreePresentation (R := R) (P := Q φ) (ι := ι)) :
    (CokernelOrderIdeal.obstructionIdeal φ b = ⊥ ↔
      ∃ n : N, φ n = b) := by
  exact obstructionIdeal_eq_bot_iff_exists φ b S

/-- Over a Noetherian base the intrinsic defect ideal is finite type, with no
frame choice in the statement. -/
theorem obstructionIdeal_fg
    [IsNoetherianRing R]
    (φ : N →ₗ[R] E) (b : E) :
    (CokernelOrderIdeal.obstructionIdeal φ b).FG :=
  CokernelOrderIdeal.obstructionIdeal_fg φ b

end

end SplitCokernelOrderIdealCompiler
end Experimental
end PCRLean
