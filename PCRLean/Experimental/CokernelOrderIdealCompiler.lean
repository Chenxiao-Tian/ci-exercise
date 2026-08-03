import Mathlib
import PCRLean.Experimental.CokernelOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealMinimality

/-!
# Exact three-way compiler for a cokernel obstruction section

Let `ω = [b] ∈ coker φ` and let

`J = O(ω)`

be its intrinsic order ideal.  For a finite dual frame on the cokernel, exactly
one of the following mutually exclusive geometric regimes holds:

1. `J = 0`: the packet is effective and has an actual graph solution;
2. `0 < J < R`: `J` is the unique minimal proper coefficient defect, the
   obstruction lies in `J · coker φ`, and this is the genuine hybrid branch;
3. `J = R`: no proper ideal can absorb all obstruction coefficients, so no
   proper order-ideal defect centre exists.

This theorem closes the logical trichotomy of X028 Step D.  It does not produce
the marked closure or prove regularity of the hybrid centre.
-/

namespace PCRLean
namespace Experimental
namespace CokernelOrderIdealCompiler

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {N : Type v} {E : Type w}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

open DeterminantalCokernelObstruction
open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal
open ProjectiveSectionOrderIdealMinimality

abbrev Q (φ : N →ₗ[R] E) := E ⧸ LinearMap.range φ

/-- The three exact order-ideal regimes. -/
inductive Status
    (φ : N →ₗ[R] E) (b : E)
    (F : DualFrame (R := R) (P := Q φ) (ι := ι)) : Type (max u v w x)
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
            CoefficientsVanishMod F (obstruction φ b) J}
          (CokernelOrderIdeal.obstructionIdeal φ b))
  | unitObstruction
      (ideal_eq_top : CokernelOrderIdeal.obstructionIdeal φ b = ⊤)
      (noProperAbsorption :
        ¬ ∃ J : Ideal R,
          J ≠ ⊤ ∧
            CoefficientsVanishMod F (obstruction φ b) J)

/-- Every finite-projective cokernel obstruction lies in exactly one branch. -/
noncomputable def compile
    (φ : N →ₗ[R] E) (b : E)
    (F : DualFrame (R := R) (P := Q φ) (ι := ι)) :
    Status φ b F := by
  classical
  by_cases hbot : CokernelOrderIdeal.obstructionIdeal φ b = ⊥
  · exact Status.graph hbot
      ((CokernelOrderIdeal.obstructionIdeal_eq_bot_iff_exists
        φ b F).mp hbot)
  · by_cases htop : CokernelOrderIdeal.obstructionIdeal φ b = ⊤
    · exact Status.unitObstruction htop
        (no_proper_ideal_absorbs_unit_obstruction
          F (obstruction φ b) htop)
    · exact Status.hybrid hbot htop
        (CokernelOrderIdeal.obstruction_mem_orderIdeal_smul_top
          φ b F)
        (orderIdeal_isLeast F (obstruction φ b))

/-- The graph branch is equivalent to exact effectivity. -/
theorem graphBranch_iff_exists_solution
    (φ : N →ₗ[R] E) (b : E)
    (F : DualFrame (R := R) (P := Q φ) (ι := ι)) :
    CokernelOrderIdeal.obstructionIdeal φ b = ⊥ ↔
      ∃ n : N, φ n = b :=
  CokernelOrderIdeal.obstructionIdeal_eq_bot_iff_exists φ b F

/-- In the hybrid branch the canonical ideal is finite type over a Noetherian
base. -/
theorem hybridIdeal_fg
    [IsNoetherianRing R]
    (φ : N →ₗ[R] E) (b : E) :
    (CokernelOrderIdeal.obstructionIdeal φ b).FG :=
  CokernelOrderIdeal.obstructionIdeal_fg φ b

end

end CokernelOrderIdealCompiler
end Experimental
end PCRLean
