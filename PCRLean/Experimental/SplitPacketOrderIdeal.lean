import Mathlib
import PCRLean.Experimental.ProjectiveMoritaDescent
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# Split packets and their canonical order-ideal defect

A split injection `φ : N → E` provides a concrete residual projector

`ρ(b) = b - φ(retract b)`.

The residual is the chosen representative of the cokernel obstruction. If the
ambient finite-projective packet module has a dual frame, the intrinsic order
ideal of `ρ(b)` is an actual finite defect component. The target always lies in

`range φ + orderIdeal(ρ(b)) • E`.

The defect ideal is zero exactly when the original packet is effective. This
turns a failed graph equation into a canonical hybrid component rather than an
arbitrary new centre choice.
-/

namespace PCRLean
namespace Experimental
namespace SplitPacketOrderIdeal

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {N : Type v} {E : Type w}
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal

/-- A linear packet map with a chosen retraction. -/
structure SplitInjection where
  map : N →ₗ[R] E
  retract : E →ₗ[R] N
  leftInverse : retract.comp map = LinearMap.id

namespace SplitInjection

variable (S : SplitInjection (R := R) (N := N) (E := E))

/-- Pointwise left inverse. -/
@[simp] theorem retract_map (x : N) : S.retract (S.map x) = x := by
  have h := congrArg (fun f : N →ₗ[R] N => f x) S.leftInverse
  simpa [LinearMap.comp_apply] using h

/-- The split packet map is injective. -/
theorem injective : Function.Injective S.map := by
  intro x y hxy
  simpa using congrArg S.retract hxy

/-- Concrete representative of the cokernel obstruction. -/
def residual (b : E) : E :=
  b - S.map (S.retract b)

/-- Retraction kills the residual. -/
theorem retract_residual (b : E) : S.retract (S.residual b) = 0 := by
  simp [residual]

/-- Exact target decomposition into image part plus residual. -/
theorem map_retract_add_residual (b : E) :
    S.map (S.retract b) + S.residual b = b := by
  simp [residual]

/-- Exact packet effectivity is equivalent to zero residual. -/
theorem residual_eq_zero_iff_mem_range (b : E) :
    S.residual b = 0 ↔ b ∈ LinearMap.range S.map := by
  constructor
  · intro hzero
    refine ⟨S.retract b, ?_⟩
    have h := S.map_retract_add_residual b
    simpa [hzero] using h.symm
  · rintro ⟨x, rfl⟩
    simp [residual]

/-- Intrinsic defect ideal of one target section. -/
def defectIdeal (b : E) : Ideal R :=
  orderIdeal (S.residual b)

/-- The target belongs to the image plus the scalar extension of its defect
ideal. -/
theorem target_mem_range_sup_defect
    (F : DualFrame (R := R) (P := E) (ι := ι))
    (b : E) :
    b ∈ LinearMap.range S.map ⊔
      S.defectIdeal b • (⊤ : Submodule R E) := by
  rw [Submodule.mem_sup]
  refine ⟨S.map (S.retract b), ?_, S.residual b, ?_, ?_⟩
  · exact LinearMap.mem_range_self S.map (S.retract b)
  · exact ProjectiveSectionOrderIdeal.section_mem_orderIdeal_smul_top
      F (S.residual b)
  · exact S.map_retract_add_residual b

/-- The defect ideal vanishes exactly when the target has an exact solution. -/
theorem defectIdeal_eq_bot_iff_effective
    (F : DualFrame (R := R) (P := E) (ι := ι))
    (b : E) :
    S.defectIdeal b = ⊥ ↔ b ∈ LinearMap.range S.map := by
  rw [defectIdeal,
    ProjectiveSectionOrderIdeal.orderIdeal_eq_bot_iff F,
    S.residual_eq_zero_iff_mem_range]

/-- Over a Noetherian base the defect component is finite type. -/
theorem defectIdeal_fg
    [IsNoetherianRing R]
    (b : E) : (S.defectIdeal b).FG :=
  ProjectiveSectionOrderIdeal.orderIdeal_fg _

end SplitInjection

end

end SplitPacketOrderIdeal
end Experimental
end PCRLean
