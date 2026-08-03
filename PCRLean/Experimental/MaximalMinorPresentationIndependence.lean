import Mathlib
import PCRLean.Experimental.MaximalMinorRangeCriterion

/-!
# Presentation independence of the maximal-minor range criterion

Two finite affine packets may use different equation frames.  Assume their row
modules are linearly equivalent and that the equivalence carries both the
packet value `M z` and the right-hand side `b` to the second presentation.
Then the two systems have exactly the same solution predicate.

If both coefficient matrices satisfy the maximal-minor cover condition, the
maximal-plus-augmented determinantal criterion is therefore invariant under
this change of presentation.  Moreover the two Čech-constructed global graph
solutions are equal, because each is the unique solution of the same intrinsic
system.

This result avoids a large Cauchy--Binet calculation: presentation independence
is derived from the already proved exact range characterization, rather than
from generatorwise comparison of all minors.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorPresentationIndependence

noncomputable section

universe u v₁ v₂ w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ₁ : Type v₁} [Fintype κ₁]
variable {κ₂ : Type v₂} [Fintype κ₂]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An intrinsic equivalence between two row presentations of the same affine
linear packet. -/
structure EquationEquivalence
    (M₁ : Matrix κ₁ ι R) (b₁ : κ₁ → R)
    (M₂ : Matrix κ₂ ι R) (b₂ : κ₂ → R) where
  rowEquiv : (κ₁ → R) ≃ₗ[R] (κ₂ → R)
  packet_commutes : ∀ z : ι → R,
    rowEquiv (M₁.mulVec z) = M₂.mulVec z
  rhs_commutes : rowEquiv b₁ = b₂

namespace EquationEquivalence

variable {M₁ : Matrix κ₁ ι R} {b₁ : κ₁ → R}
variable {M₂ : Matrix κ₂ ι R} {b₂ : κ₂ → R}
variable (E : EquationEquivalence M₁ b₁ M₂ b₂)

/-- The two presentations have exactly the same solutions. -/
theorem solution_iff (z : ι → R) :
    M₁.mulVec z = b₁ ↔ M₂.mulVec z = b₂ := by
  constructor
  · intro h
    calc
      M₂.mulVec z = E.rowEquiv (M₁.mulVec z) :=
        (E.packet_commutes z).symm
      _ = E.rowEquiv b₁ := by rw [h]
      _ = b₂ := E.rhs_commutes
  · intro h
    apply E.rowEquiv.injective
    calc
      E.rowEquiv (M₁.mulVec z) = M₂.mulVec z :=
        E.packet_commutes z
      _ = b₂ := h
      _ = E.rowEquiv b₁ := E.rhs_commutes.symm

/-- Existence of a solution is presentation independent. -/
theorem exists_solution_iff :
    (∃ z : ι → R, M₁.mulVec z = b₁) ↔
      ∃ z : ι → R, M₂.mulVec z = b₂ := by
  exact exists_congr E.solution_iff

/-- Unique solvability is presentation independent. -/
theorem existsUnique_solution_iff :
    (∃! z : ι → R, M₁.mulVec z = b₁) ↔
      ∃! z : ι → R, M₂.mulVec z = b₂ := by
  constructor
  · rintro ⟨z, hz, hu⟩
    refine ⟨z, (E.solution_iff z).mp hz, ?_⟩
    intro y hy
    exact hu y ((E.solution_iff y).mpr hy)
  · rintro ⟨z, hz, hu⟩
    refine ⟨z, (E.solution_iff z).mpr hz, ?_⟩
    intro y hy
    exact hu y ((E.solution_iff y).mp hy)

variable
  (H₁ : MaximalMinorAtlas.FullRankCover M₁)
  (H₂ : MaximalMinorAtlas.FullRankCover M₂)

/-- The finite maximal-plus-augmented minor condition is invariant under an
intrinsic row-presentation equivalence. -/
theorem augmentedRankCondition_iff :
    MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁ ↔
      MaximalMinorAugmentedPacket.AugmentedRankCondition M₂ b₂ := by
  rw [MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        M₁ b₁ H₁,
      MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        M₂ b₂ H₂]
  exact E.exists_solution_iff

/-- Transport an augmented-rank certificate to the second presentation. -/
noncomputable def transportAugmented
    (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁) :
    MaximalMinorAugmentedPacket.AugmentedRankCondition M₂ b₂ :=
  (E.augmentedRankCondition_iff H₁ H₂).mp Haug

/-- The global graph extracted from the two presentations is the same actual
tuple. -/
theorem globalGraph_eq
    (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition M₁ b₁) :
    Haug.globalGraph H₁ =
      (E.transportAugmented H₁ H₂ Haug).globalGraph H₂ := by
  let Haug₂ := E.transportAugmented H₁ H₂ Haug
  have h₁ : M₁.mulVec (Haug.globalGraph H₁) = b₁ :=
    Haug.globalGraph_solves H₁
  have h₂ : M₂.mulVec (Haug.globalGraph H₁) = b₂ :=
    (E.solution_iff (Haug.globalGraph H₁)).mp h₁
  exact Haug₂.solution_eq_globalGraph H₂ h₂

end EquationEquivalence

end

end MaximalMinorPresentationIndependence
end Experimental
end PCRLean
