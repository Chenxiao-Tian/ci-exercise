import Mathlib
import PCRLean.Experimental.MaximalMinorRangeCriterion

/-!
# Affine row-and-variable naturality of the maximal-minor criterion

The determinantal centre must not depend on either the equation frame or the
chosen normal-coordinate frame.  Two finite affine packets are intrinsically
equivalent when:

* their normal free modules are related by a linear equivalence `e`;
* their equation-row modules are related by a linear equivalence `f`;
* applying the first packet and then `f` agrees with first changing variables
  by `e` and then applying the second packet; and
* `f` carries the first right-hand side to the second.

The solution spaces are then equivalent by `e`.  If both coordinate
presentations satisfy the maximal-minor cover condition, the augmented-minor
criterion is equivalent in the two presentations, and the two globally glued
solutions correspond exactly under `e`.

This establishes presentation independence at the level of both row and normal
coordinate changes without comparing individual determinants by Cauchy--Binet.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorAffineEquivalence

noncomputable section

universe u v₁ v₂ w₁ w₂

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ₁ : Type v₁} [Fintype κ₁]
variable {κ₂ : Type v₂} [Fintype κ₂]
variable {ι₁ : Type w₁} [Fintype ι₁] [DecidableEq ι₁] [Nonempty ι₁]
variable {ι₂ : Type w₂} [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂]

/-- Intrinsic equivalence of two affine packet presentations. -/
structure PacketEquivalence
    (M₁ : Matrix κ₁ ι₁ R) (b₁ : κ₁ → R)
    (M₂ : Matrix κ₂ ι₂ R) (b₂ : κ₂ → R) where
  variableEquiv : (ι₁ → R) ≃ₗ[R] (ι₂ → R)
  rowEquiv : (κ₁ → R) ≃ₗ[R] (κ₂ → R)
  packet_commutes : ∀ z : ι₁ → R,
    rowEquiv (M₁.mulVec z) = M₂.mulVec (variableEquiv z)
  rhs_commutes : rowEquiv b₁ = b₂

namespace PacketEquivalence

variable {M₁ : Matrix κ₁ ι₁ R} {b₁ : κ₁ → R}
variable {M₂ : Matrix κ₂ ι₂ R} {b₂ : κ₂ → R}
variable (E : PacketEquivalence M₁ b₁ M₂ b₂)

/-- Changing both equation and variable frames preserves the solution
predicate. -/
theorem solution_iff (z : ι₁ → R) :
    M₁.mulVec z = b₁ ↔
      M₂.mulVec (E.variableEquiv z) = b₂ := by
  constructor
  · intro h
    calc
      M₂.mulVec (E.variableEquiv z) = E.rowEquiv (M₁.mulVec z) :=
        (E.packet_commutes z).symm
      _ = E.rowEquiv b₁ := by rw [h]
      _ = b₂ := E.rhs_commutes
  · intro h
    apply E.rowEquiv.injective
    calc
      E.rowEquiv (M₁.mulVec z) =
          M₂.mulVec (E.variableEquiv z) := E.packet_commutes z
      _ = b₂ := h
      _ = E.rowEquiv b₁ := E.rhs_commutes.symm

/-- Inverse-frame form of the solution equivalence. -/
theorem inverse_solution_iff (z : ι₂ → R) :
    M₁.mulVec (E.variableEquiv.symm z) = b₁ ↔
      M₂.mulVec z = b₂ := by
  simpa using E.solution_iff (E.variableEquiv.symm z)

/-- Existence of a solution is invariant under the affine packet equivalence. -/
theorem exists_solution_iff :
    (∃ z : ι₁ → R, M₁.mulVec z = b₁) ↔
      ∃ z : ι₂ → R, M₂.mulVec z = b₂ := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨E.variableEquiv z, (E.solution_iff z).mp hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨E.variableEquiv.symm z,
      (E.inverse_solution_iff z).mpr hz⟩

/-- Unique solvability is invariant under the affine packet equivalence. -/
theorem existsUnique_solution_iff :
    (∃! z : ι₁ → R, M₁.mulVec z = b₁) ↔
      ∃! z : ι₂ → R, M₂.mulVec z = b₂ := by
  constructor
  · rintro ⟨z, hz, hu⟩
    refine ⟨E.variableEquiv z, (E.solution_iff z).mp hz, ?_⟩
    intro y hy
    have hpre : E.variableEquiv.symm y = z :=
      hu (E.variableEquiv.symm y)
        ((E.inverse_solution_iff y).mpr hy)
    simpa using congrArg E.variableEquiv hpre
  · rintro ⟨z, hz, hu⟩
    refine ⟨E.variableEquiv.symm z,
      (E.inverse_solution_iff z).mpr hz, ?_⟩
    intro y hy
    have himage : E.variableEquiv y = z :=
      hu (E.variableEquiv y) ((E.solution_iff y).mp hy)
    simpa using congrArg E.variableEquiv.symm himage

variable
  (H₁ : MaximalMinorAtlas.FullRankCover M₁)
  (H₂ : MaximalMinorAtlas.FullRankCover M₂)

/-- Once both coordinate presentations are recognized as full-rank, the finite
augmented-minor condition is intrinsic. -/
theorem augmentedRankCondition_iff :
    MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁ ↔
      MaximalMinorAugmentedPacket.AugmentedRankCondition M₂ b₂ := by
  rw [MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        M₁ b₁ H₁,
      MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        M₂ b₂ H₂]
  exact E.exists_solution_iff

/-- Transport an augmented-rank certificate across both frame changes. -/
noncomputable def transportAugmented
    (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁) :
    MaximalMinorAugmentedPacket.AugmentedRankCondition M₂ b₂ :=
  (E.augmentedRankCondition_iff H₁ H₂).mp Haug

/-- The two Čech-constructed global graph solutions correspond exactly under
the normal-coordinate equivalence. -/
theorem globalGraph_eq
    (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁) :
    E.variableEquiv (Haug.globalGraph H₁) =
      (E.transportAugmented H₁ H₂ Haug).globalGraph H₂ := by
  let Haug₂ := E.transportAugmented H₁ H₂ Haug
  have h₁ : M₁.mulVec (Haug.globalGraph H₁) = b₁ :=
    Haug.globalGraph_solves H₁
  have h₂ :
      M₂.mulVec (E.variableEquiv (Haug.globalGraph H₁)) = b₂ :=
    (E.solution_iff (Haug.globalGraph H₁)).mp h₁
  exact Haug₂.solution_eq_globalGraph H₂ h₂

end PacketEquivalence

end

end MaximalMinorAffineEquivalence
end Experimental
end PCRLean
