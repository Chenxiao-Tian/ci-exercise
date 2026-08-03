import Mathlib
import PCRLean.FunctionalPacketIdeal
import PCRLean.Experimental.DualPacketAffineLinearRealization
import PCRLean.Experimental.MaximalMinorRangeCriterion

/-!
# Coordinate realization of finite affine conormal packets

Let `V` be a finite free tangent/conormal model over a field and let

`λ_r : V → K`, `c_r : K`

be a finite affine covector packet.  An explicit linear coordinate frame

`E : V ≃ₗ[K] (σ → K)`

produces the rectangular matrix

`M_{ri} = λ_r(E⁻¹ e_i)`.

This file proves that the intrinsic affine equations

`λ_r(v) = c_r`

are exactly the coordinate matrix equations

`M · E(v) = c`.

Consequently, if the coordinate matrix satisfies the maximal-minor cover and
augmented-minor consistency conditions, the determinantal global graph pulls
back through `E` to a unique intrinsic solution in `V`.  Changing the coordinate
frame changes only the matrix presentation, not the intrinsic solution.

This is the bridge from finite conormal/Frobenius packet data to the canonical
matrix compiler.  It does not yet construct the packet from an arbitrary
resolution state or prove the determinantal conditions universally.
-/

namespace PCRLean
namespace Experimental
namespace ConormalAffinePacketCoordinates

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {κ : Type w} [Fintype κ]
variable {σ : Type x} [Fintype σ] [DecidableEq σ] [Nonempty σ]

abbrev Coord := σ → K
abbrev DualV := Module.Dual K V

/-- Finite affine conormal packet. -/
structure Packet where
  row : κ → DualV (K := K) (V := V)
  rhs : κ → K

namespace Packet

variable (P : Packet (K := K) (V := V) (κ := κ))
variable (E : V ≃ₗ[K] Coord (K := K) (σ := σ))

/-- A packet row transported to the coordinate vector space. -/
def coordinateFunctional (r : κ) :
    Module.Dual K (Coord (K := K) (σ := σ)) :=
  (P.row r).comp E.symm.toLinearMap

/-- Coordinate matrix of the conormal packet. -/
def matrix : Matrix κ σ K :=
  fun r i => P.coordinateFunctional E r
    (FunctionalPacketIdeal.basisVector (K := K) i)

/-- Intrinsic packet evaluation. -/
def evaluate (v : V) : κ → K :=
  fun r => P.row r v

/-- Coordinate packet evaluation. -/
def coordinateEvaluate (z : Coord (K := K) (σ := σ)) : κ → K :=
  (P.matrix E).mulVec z

/-- One coordinate matrix row evaluates exactly the corresponding intrinsic
covector. -/
theorem matrix_mulVec_coordinate_apply
    (v : V) (r : κ) :
    (P.matrix E).mulVec (E v) r = P.row r v := by
  have hx := congrArg (P.coordinateFunctional E r)
    (DualPacketAffineLinearRealization.direction_eq_sum_basisVector
      (K := K) (σ := σ) (E v))
  simpa [matrix, coordinateFunctional, Matrix.mulVec, dotProduct,
    mul_comm] using hx.symm

/-- Simultaneous coordinate/intrinsic evaluation equality. -/
theorem matrix_mulVec_coordinate (v : V) :
    (P.matrix E).mulVec (E v) = P.evaluate v := by
  funext r
  exact P.matrix_mulVec_coordinate_apply E v r

/-- The intrinsic affine equations and coordinate matrix equations are
identical. -/
theorem solution_iff (v : V) :
    P.evaluate v = P.rhs ↔
      (P.matrix E).mulVec (E v) = P.rhs := by
  rw [P.matrix_mulVec_coordinate E]

/-- Inverse-coordinate form of the same equivalence. -/
theorem coordinate_solution_iff
    (z : Coord (K := K) (σ := σ)) :
    P.evaluate (E.symm z) = P.rhs ↔
      (P.matrix E).mulVec z = P.rhs := by
  simpa using P.solution_iff E (E.symm z)

variable [IsNoetherianRing K] [IsRegularRing K]
variable (Hrank : MaximalMinorAtlas.FullRankCover (P.matrix E))
variable (Haug :
  MaximalMinorAugmentedPacket.AugmentedRankCondition
    (P.matrix E) P.rhs)

/-- Coordinate solution supplied by the determinantal compiler. -/
noncomputable def coordinateSolution : Coord (K := K) (σ := σ) :=
  Haug.globalGraph Hrank

/-- Intrinsic solution obtained by returning through the coordinate frame. -/
noncomputable def intrinsicSolution : V :=
  E.symm (P.coordinateSolution E Hrank Haug)

/-- The reconstructed intrinsic vector satisfies every conormal equation. -/
theorem intrinsicSolution_solves :
    P.evaluate (P.intrinsicSolution E Hrank Haug) = P.rhs := by
  apply (P.coordinate_solution_iff E
    (P.coordinateSolution E Hrank Haug)).mpr
  exact Haug.globalGraph_solves Hrank

/-- The intrinsic conormal solution is unique. -/
theorem solution_eq_intrinsicSolution
    {v : V} (hv : P.evaluate v = P.rhs) :
    v = P.intrinsicSolution E Hrank Haug := by
  apply E.injective
  apply Haug.solution_eq_globalGraph Hrank
  exact (P.solution_iff E v).mp hv

/-- Exact intrinsic existence-and-uniqueness theorem. -/
theorem existsUnique_intrinsicSolution :
    ∃! v : V, P.evaluate v = P.rhs := by
  refine ⟨P.intrinsicSolution E Hrank Haug,
    P.intrinsicSolution_solves E Hrank Haug, ?_⟩
  intro v hv
  exact P.solution_eq_intrinsicSolution E Hrank Haug hv

end Packet

end

end ConormalAffinePacketCoordinates
end Experimental
end PCRLean
