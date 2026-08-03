import Mathlib
import PCRLean.Experimental.CokernelOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealBaseChange

/-!
# Compatible base change of cokernel obstruction ideals

For two affine packet maps over `R` and `S`, suppose we have:

* a linear map between their cokernels;
* an equality carrying the source obstruction class to the target obstruction
  class; and
* compatible finite dual frames on the two cokernels.

Then the canonical order ideal of the obstruction transports exactly by ideal
extension:

`O_{coker φ_S}([b_S]) = O_{coker φ_R}([b_R]) S`.

Under faithful flatness, vanishing of the obstruction ideal is equivalent on
both sides. This isolates the precise remaining geometric task for
localization and overlap descent: construct the cokernel comparison map and
its compatible frame, rather than reproving determinantal formulas chart by
chart.
-/

namespace PCRLean
namespace Experimental
namespace CokernelOrderIdealBaseChange

noncomputable section

universe u v w x y z a

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

variable {NR : Type w} {ER : Type x}
variable [AddCommGroup NR] [Module R NR]
variable [AddCommGroup ER] [Module R ER]

variable {NS : Type y} {ES : Type z}
variable [AddCommGroup NS] [Module S NS]
variable [AddCommGroup ES] [Module S ES]
variable [Module R ES] [IsScalarTower R S ES]

variable {ι : Type a} [Fintype ι] [DecidableEq ι]

open DeterminantalCokernelObstruction
open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal
open ProjectiveSectionOrderIdealBaseChange

abbrev QR (φ : NR →ₗ[R] ER) := ER ⧸ LinearMap.range φ
abbrev QS (φ : NS →ₗ[S] ES) := ES ⧸ LinearMap.range φ

/-- Exact data required to compare two cokernel obstruction sections. -/
structure CompatibleObstructions
    (φR : NR →ₗ[R] ER) (bR : ER)
    (φS : NS →ₗ[S] ES) (bS : ES)
    (FR : DualFrame (R := R) (P := QR φR) (ι := ι))
    (FS : DualFrame (R := S) (P := QS φS) (ι := ι)) where
  map : QR φR →ₗ[R] QS φS
  obstruction_map :
    map (obstruction φR bR) = obstruction φS bS
  coefficient : ∀ i x,
    FS.functional i (map x) = algebraMap R S (FR.functional i x)

namespace CompatibleObstructions

variable
  {φR : NR →ₗ[R] ER} {bR : ER}
  {φS : NS →ₗ[S] ES} {bS : ES}
  {FR : DualFrame (R := R) (P := QR φR) (ι := ι)}
  {FS : DualFrame (R := S) (P := QS φS) (ι := ι)}
  (C : CompatibleObstructions φR bR φS bS FR FS)

/-- Forget the cokernel origin and retain the compatible section frames. -/
def toCompatibleFrames :
    ProjectiveSectionOrderIdealBaseChange.CompatibleFrames FR FS where
  map := C.map
  coefficient := C.coefficient

/-- Main exact transport theorem for the canonical cokernel defect ideal. -/
theorem map_obstructionIdeal_eq :
    Ideal.map (algebraMap R S)
        (CokernelOrderIdeal.obstructionIdeal φR bR) =
      CokernelOrderIdeal.obstructionIdeal φS bS := by
  have h := C.toCompatibleFrames.map_orderIdeal_eq
    (obstruction φR bR)
  rw [C.obstruction_map] at h
  exact h

/-- Vanishing of the source obstruction ideal implies vanishing after the
compatible base change. -/
theorem target_eq_bot_of_source_eq_bot
    (hR : CokernelOrderIdeal.obstructionIdeal φR bR = ⊥) :
    CokernelOrderIdeal.obstructionIdeal φS bS = ⊥ := by
  rw [← C.map_obstructionIdeal_eq, hR, Ideal.map_bot]

/-- Faithful flatness reflects vanishing of the cokernel order ideal. -/
theorem source_eq_bot_of_target_eq_bot
    [Module.FaithfullyFlat R S]
    (hS : CokernelOrderIdeal.obstructionIdeal φS bS = ⊥) :
    CokernelOrderIdeal.obstructionIdeal φR bR = ⊥ := by
  have htarget :
      ProjectiveSectionOrderIdeal.orderIdeal
          (C.map (obstruction φR bR)) = ⊥ := by
    rw [C.obstruction_map]
    exact hS
  exact C.toCompatibleFrames.source_orderIdeal_eq_bot_of_target_eq_bot
    (obstruction φR bR) htarget

/-- Under faithful flatness, effectivity detected by the canonical order ideal
is equivalent before and after compatible cokernel base change. -/
theorem obstructionIdeal_eq_bot_iff
    [Module.FaithfullyFlat R S] :
    CokernelOrderIdeal.obstructionIdeal φS bS = ⊥ ↔
      CokernelOrderIdeal.obstructionIdeal φR bR = ⊥ := by
  constructor
  · exact C.source_eq_bot_of_target_eq_bot
  · exact C.target_eq_bot_of_source_eq_bot

end CompatibleObstructions

end

end CokernelOrderIdealBaseChange
end Experimental
end PCRLean
