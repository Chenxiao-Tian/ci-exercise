import Mathlib
import PCRLean.Experimental.ConormalAffinePacketOverRing
import PCRLean.Experimental.ProjectiveMoritaDescent
import PCRLean.Experimental.ProjectiveSectionOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealMinimality
import PCRLean.Experimental.SplitPacketOrderIdeal
import PCRLean.Experimental.AffinePacketHybridEffectivity

/-!
# Split matrix packets and canonical order-ideal hybrid centres

Let `M : κ × ι → R` define a linear packet map

`M : R^ι → R^κ`

and assume a chosen left inverse `L : R^κ → R^ι`.  For a target `b`, the graph
candidate is `h = L b` and the residual is

`ρ = b - M h`.

The standard coordinate dual frame on `R^κ` makes the intrinsic order ideal

`J = O(ρ)`

an explicit finite coefficient defect.  Every residual coordinate lies in `J`,
so the complete affine packet ideal lies in the actual hybrid centre

`(Z_i-h_i) + J R[Z]`.

All `q`-th power owners are therefore marked-permissible for the same hybrid
centre.  Moreover:

* `J=0` iff the original packet is exactly effective;
* `J=⊤` admits no proper coefficient ideal absorbing all residual rows; and
* `0<J<R` is the canonical genuine graph-plus-defect chamber.

This is the finite free model of the X028 order-ideal hybrid compiler.
-/

namespace PCRLean
namespace Experimental
namespace SplitMatrixOrderIdealHybrid

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Source := ι → R
abbrev Target := κ → R

/-- Standard basis vector in the target packet module. -/
def targetBasisVector (i : κ) : Target (R := R) (κ := κ) :=
  fun j => if j = i then 1 else 0

/-- Coordinate functional on the target packet module. -/
def targetCoordinateFunctional (i : κ) :
    Module.Dual R (Target (R := R) (κ := κ)) where
  toFun x := x i
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- Standard finite dual frame on `R^κ`. -/
def targetFrame :
    ProjectiveMoritaDescent.DualFrame
      (R := R) (P := Target (R := R) (κ := κ)) (ι := κ) where
  vector := targetBasisVector
  functional := targetCoordinateFunctional
  reconstruct := by
    intro x
    funext j
    simp [targetBasisVector, targetCoordinateFunctional]

/-- Linear packet map associated to a rectangular matrix. -/
def matrixMap (M : Matrix κ ι R) :
    Source (R := R) (ι := ι) →ₗ[R] Target (R := R) (κ := κ) where
  toFun := M.mulVec
  map_add' := by
    intro x y
    funext r
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  map_smul' := by
    intro a x
    funext r
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- A rectangular packet together with a chosen left inverse. -/
structure SplitPacket (M : Matrix κ ι R) where
  retract : Target (R := R) (κ := κ) →ₗ[R] Source (R := R) (ι := ι)
  leftInverse : retract.comp (matrixMap M) = LinearMap.id

namespace SplitPacket

variable {M : Matrix κ ι R}
    (S : SplitPacket M)

/-- Standard split-injection package. -/
def toSplitInjection :
    SplitPacketOrderIdeal.SplitInjection
      (R := R)
      (N := Source (R := R) (ι := ι))
      (E := Target (R := R) (κ := κ)) where
  map := matrixMap M
  retract := S.retract
  leftInverse := S.leftInverse

/-- Canonical graph candidate. -/
def graph (b : Target (R := R) (κ := κ)) :
    Source (R := R) (ι := ι) :=
  S.retract b

/-- Canonical residual obstruction. -/
def residual (b : Target (R := R) (κ := κ)) :
    Target (R := R) (κ := κ) :=
  b - M.mulVec (S.graph b)

/-- Residual agrees with the generic split-injection residual. -/
theorem residual_eq_splitResidual
    (b : Target (R := R) (κ := κ)) :
    S.residual b = S.toSplitInjection.residual b := by
  rfl

/-- Canonical coefficient defect ideal. -/
def defectIdeal (b : Target (R := R) (κ := κ)) : Ideal R :=
  ProjectiveSectionOrderIdeal.orderIdeal (S.residual b)

/-- The defect ideal is the generic split-packet order ideal. -/
theorem defectIdeal_eq_splitDefectIdeal
    (b : Target (R := R) (κ := κ)) :
    S.defectIdeal b = S.toSplitInjection.defectIdeal b := by
  rfl

/-- Every residual coordinate belongs to the canonical defect ideal. -/
theorem residual_coordinate_mem
    (b : Target (R := R) (κ := κ)) (r : κ) :
    S.residual b r ∈ S.defectIdeal b := by
  exact Ideal.subset_span
    ⟨targetCoordinateFunctional (R := R) r, rfl⟩

/-- Residual equation in the graph convention used by the hybrid compiler. -/
theorem graph_residual_eq_neg
    (b : Target (R := R) (κ := κ)) (r : κ) :
    (M.mulVec (S.graph b)) r - b r = -(S.residual b r) := by
  rfl

/-- Every graph residual row lies in the canonical defect ideal. -/
theorem graph_residual_mem_defectIdeal
    (b : Target (R := R) (κ := κ)) (r : κ) :
    (M.mulVec (S.graph b)) r - b r ∈ S.defectIdeal b := by
  rw [S.graph_residual_eq_neg b r]
  exact (S.defectIdeal b).neg_mem (S.residual_coordinate_mem b r)

/-- The complete affine packet ideal lies in the canonical graph-plus-order-
ideal hybrid centre. -/
theorem equationIdeal_le_hybridIdeal
    (b : Target (R := R) (κ := κ)) :
    MaximalMinorEquationIdeal.equationIdeal M b ≤
      AffinePacketHybridEffectivity.hybridIdeal
        (S.defectIdeal b) (S.graph b) := by
  exact AffinePacketHybridEffectivity.equationIdeal_le_hybridIdeal
    M b (S.graph b) (S.defectIdeal b)
    (S.graph_residual_mem_defectIdeal b)

/-- Every `q`-th power packet owner is permissible for the same canonical
hybrid centre. -/
theorem poweredEquationIdeal_le_hybridIdeal_pow
    (b : Target (R := R) (κ := κ)) (q : Nat) :
    AffinePacketHybridEffectivity.poweredEquationIdeal M b q ≤
      (AffinePacketHybridEffectivity.hybridIdeal
        (S.defectIdeal b) (S.graph b)) ^ q := by
  exact AffinePacketHybridEffectivity.poweredEquationIdeal_le_hybridIdeal_pow
    M b (S.graph b) (S.defectIdeal b)
    (S.graph_residual_mem_defectIdeal b) q

/-- Zero canonical defect is exactly packet effectivity. -/
theorem defectIdeal_eq_bot_iff_exists_solution
    (b : Target (R := R) (κ := κ)) :
    S.defectIdeal b = ⊥ ↔
      ∃ x : Source (R := R) (ι := ι), M.mulVec x = b := by
  rw [S.defectIdeal_eq_splitDefectIdeal]
  exact S.toSplitInjection.defectIdeal_eq_bot_iff_effective
    (targetFrame (R := R) (κ := κ)) b |>.trans LinearMap.mem_range

/-- Unit defect no-go: no proper coefficient ideal can absorb every residual
coordinate. -/
theorem no_proper_ideal_absorbs_residual
    (b : Target (R := R) (κ := κ))
    (htop : S.defectIdeal b = ⊤) :
    ¬ ∃ J : Ideal R,
      J ≠ ⊤ ∧ ∀ r : κ, S.residual b r ∈ J := by
  have htop' :
      ProjectiveSectionOrderIdeal.orderIdeal (S.residual b) = ⊤ := htop
  exact ProjectiveSectionOrderIdealMinimality.no_proper_ideal_absorbs_unit_obstruction
    (targetFrame (R := R) (κ := κ)) (S.residual b) htop'

end SplitPacket

end

end SplitMatrixOrderIdealHybrid
end Experimental
end PCRLean
