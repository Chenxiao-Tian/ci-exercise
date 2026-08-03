import Mathlib
import PCRLean.Experimental.ConormalAffinePacketCoordinates

/-!
# Coordinate-frame independence of affine conormal packets

A finite intrinsic affine conormal packet may be written in many finite linear
coordinate frames.  Once the coordinate matrices satisfy their maximal-minor
cover conditions, the augmented-minor consistency condition is independent of
the chosen frame: in every frame it is equivalent to existence of one
intrinsic solution of the same conormal equations.

If the condition holds, the determinantal global graphs from any two frames
pull back to exactly the same vector of the intrinsic module `V`.

This removes the final coordinate choice from the current finite conormal
packet compiler.  What remains is the geometric construction and hereditary
transport of the intrinsic packet itself.
-/

namespace PCRLean
namespace Experimental
namespace ConormalPacketFrameIndependence

noncomputable section

universe u v w x₁ x₂

variable {K : Type u} [Field K]
variable [IsNoetherianRing K] [IsRegularRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {κ : Type w} [Fintype κ]
variable {σ₁ : Type x₁} [Fintype σ₁] [DecidableEq σ₁] [Nonempty σ₁]
variable {σ₂ : Type x₂} [Fintype σ₂] [DecidableEq σ₂] [Nonempty σ₂]

open ConormalAffinePacketCoordinates

variable (P : Packet (K := K) (V := V) (κ := κ))
variable (E₁ : V ≃ₗ[K] (σ₁ → K))
variable (E₂ : V ≃ₗ[K] (σ₂ → K))
variable
  (H₁ : MaximalMinorAtlas.FullRankCover (P.matrix E₁))
  (H₂ : MaximalMinorAtlas.FullRankCover (P.matrix E₂))

/-- Coordinate solution existence in the first frame is equivalent to
intrinsic solution existence. -/
theorem first_exists_solution_iff_intrinsic :
    (∃ z : σ₁ → K, (P.matrix E₁).mulVec z = P.rhs) ↔
      ∃ v : V, P.evaluate v = P.rhs := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨E₁.symm z, (P.coordinate_solution_iff E₁ z).mpr hz⟩
  · rintro ⟨v, hv⟩
    exact ⟨E₁ v, (P.solution_iff E₁ v).mp hv⟩

/-- The analogous equivalence for the second frame. -/
theorem second_exists_solution_iff_intrinsic :
    (∃ z : σ₂ → K, (P.matrix E₂).mulVec z = P.rhs) ↔
      ∃ v : V, P.evaluate v = P.rhs := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨E₂.symm z, (P.coordinate_solution_iff E₂ z).mpr hz⟩
  · rintro ⟨v, hv⟩
    exact ⟨E₂ v, (P.solution_iff E₂ v).mp hv⟩

/-- Augmented-minor consistency is independent of the coordinate frame. -/
theorem augmentedRankCondition_iff :
    MaximalMinorAugmentedPacket.AugmentedRankCondition
        (P.matrix E₁) P.rhs ↔
      MaximalMinorAugmentedPacket.AugmentedRankCondition
        (P.matrix E₂) P.rhs := by
  rw [MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        (P.matrix E₁) P.rhs H₁,
      MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        (P.matrix E₂) P.rhs H₂,
      P.first_exists_solution_iff_intrinsic E₁,
      P.second_exists_solution_iff_intrinsic E₂]

/-- Transport a determinantal certificate between coordinate frames. -/
noncomputable def transportAugmented
    (Haug₁ : MaximalMinorAugmentedPacket.AugmentedRankCondition
      (P.matrix E₁) P.rhs) :
    MaximalMinorAugmentedPacket.AugmentedRankCondition
      (P.matrix E₂) P.rhs :=
  (P.augmentedRankCondition_iff E₁ E₂ H₁ H₂).mp Haug₁

/-- Determinantal solutions from two coordinate frames give the same intrinsic
vector. -/
theorem intrinsicSolution_eq
    (Haug₁ : MaximalMinorAugmentedPacket.AugmentedRankCondition
      (P.matrix E₁) P.rhs) :
    P.intrinsicSolution E₁ H₁ Haug₁ =
      P.intrinsicSolution E₂ H₂
        (P.transportAugmented E₁ E₂ H₁ H₂ Haug₁) := by
  apply P.solution_eq_intrinsicSolution E₁ H₁ Haug₁
  exact P.intrinsicSolution_solves E₂ H₂
    (P.transportAugmented E₁ E₂ H₁ H₂ Haug₁)

/-- Coordinate global graphs are related by the change-of-frame map. -/
theorem coordinateGraphs_correspond
    (Haug₁ : MaximalMinorAugmentedPacket.AugmentedRankCondition
      (P.matrix E₁) P.rhs) :
    E₂ (E₁.symm (Haug₁.globalGraph H₁)) =
      (P.transportAugmented E₁ E₂ H₁ H₂ Haug₁).globalGraph H₂ := by
  have h := congrArg E₂
    (P.intrinsicSolution_eq E₁ E₂ H₁ H₂ Haug₁)
  simpa [ConormalAffinePacketCoordinates.Packet.intrinsicSolution,
    ConormalAffinePacketCoordinates.Packet.coordinateSolution] using h

end

end ConormalPacketFrameIndependence
end Experimental
end PCRLean
