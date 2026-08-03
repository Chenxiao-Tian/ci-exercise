import Mathlib
import PCRLean.Experimental.MaximalMinorRangeCriterion

/-!
# Affine conormal packets over a regular coefficient ring

The field-valued coordinate compiler is not sufficient for geometric graph
centres: the right-hand sides are functions of passive coordinates and therefore
live in a regular coefficient ring `R`.

Let `V` be an `R`-module with an explicit finite coordinate frame

`E : V ≃ₗ[R] (σ → R)`

and let `λ_r : V → R`, `c_r : R` be a finite affine conormal packet.  The
coordinate matrix

`M_{ri} = λ_r(E⁻¹ e_i)`

satisfies

`M · E(v) = (λ_r(v))_r`.

Over a Noetherian regular domain, maximal-minor cover and augmented-minor
consistency therefore produce a unique intrinsic solution in `V`, with no field
hypothesis.  This is the form needed when the passive coordinate algebra is the
base ring of a polynomial graph centre.
-/

namespace PCRLean
namespace Experimental
namespace ConormalAffinePacketOverRing

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]
variable {σ : Type x} [Fintype σ] [DecidableEq σ] [Nonempty σ]

abbrev Coord := σ → R
abbrev DualV := Module.Dual R V

/-- Standard coordinate basis vector over an arbitrary commutative ring. -/
def basisVector (i : σ) : Coord (R := R) (σ := σ) :=
  fun j => if j = i then 1 else 0

/-- Finite coordinate reconstruction. -/
theorem coordinate_eq_sum_basisVector
    (z : Coord (R := R) (σ := σ)) :
    z = ∑ i : σ, z i • basisVector (R := R) i := by
  funext j
  simp [basisVector, eq_comm]

/-- Finite affine conormal packet over the coefficient ring. -/
structure Packet where
  row : κ → DualV (R := R) (V := V)
  rhs : κ → R

namespace Packet

variable (P : Packet (R := R) (V := V) (κ := κ))
variable (E : V ≃ₗ[R] Coord (R := R) (σ := σ))

/-- Packet row transported to coordinate space. -/
def coordinateFunctional (r : κ) :
    Module.Dual R (Coord (R := R) (σ := σ)) :=
  (P.row r).comp E.symm.toLinearMap

/-- Rectangular coordinate matrix. -/
def matrix : Matrix κ σ R :=
  fun r i => P.coordinateFunctional E r (basisVector (R := R) i)

/-- Intrinsic packet evaluation. -/
def evaluate (v : V) : κ → R :=
  fun r => P.row r v

/-- Coordinate matrix evaluation. -/
def coordinateEvaluate (z : Coord (R := R) (σ := σ)) : κ → R :=
  (P.matrix E).mulVec z

/-- One coordinate row evaluates the corresponding intrinsic functional. -/
theorem matrix_mulVec_coordinate_apply
    (v : V) (r : κ) :
    (P.matrix E).mulVec (E v) r = P.row r v := by
  have hz := congrArg (P.coordinateFunctional E r)
    (coordinate_eq_sum_basisVector (R := R) (σ := σ) (E v))
  simpa [matrix, coordinateFunctional, Matrix.mulVec, dotProduct,
    mul_comm] using hz.symm

/-- Simultaneous coordinate/intrinsic evaluation equality. -/
theorem matrix_mulVec_coordinate (v : V) :
    (P.matrix E).mulVec (E v) = P.evaluate v := by
  funext r
  exact P.matrix_mulVec_coordinate_apply E v r

/-- Intrinsic and coordinate solution predicates are identical. -/
theorem solution_iff (v : V) :
    P.evaluate v = P.rhs ↔
      (P.matrix E).mulVec (E v) = P.rhs := by
  rw [P.matrix_mulVec_coordinate E]

/-- Inverse-coordinate form. -/
theorem coordinate_solution_iff
    (z : Coord (R := R) (σ := σ)) :
    P.evaluate (E.symm z) = P.rhs ↔
      (P.matrix E).mulVec z = P.rhs := by
  simpa using P.solution_iff E (E.symm z)

variable (Hrank : MaximalMinorAtlas.FullRankCover (P.matrix E))
variable (Haug :
  MaximalMinorAugmentedPacket.AugmentedRankCondition
    (P.matrix E) P.rhs)

/-- Coordinate determinantal solution. -/
noncomputable def coordinateSolution : Coord (R := R) (σ := σ) :=
  Haug.globalGraph Hrank

/-- Intrinsic solution in the conormal module. -/
noncomputable def intrinsicSolution : V :=
  E.symm (P.coordinateSolution E Hrank Haug)

/-- The reconstructed vector satisfies the complete affine packet. -/
theorem intrinsicSolution_solves :
    P.evaluate (P.intrinsicSolution E Hrank Haug) = P.rhs := by
  apply (P.coordinate_solution_iff E
    (P.coordinateSolution E Hrank Haug)).mpr
  exact Haug.globalGraph_solves Hrank

/-- Uniqueness in the intrinsic module. -/
theorem solution_eq_intrinsicSolution
    {v : V} (hv : P.evaluate v = P.rhs) :
    v = P.intrinsicSolution E Hrank Haug := by
  apply E.injective
  apply Haug.solution_eq_globalGraph Hrank
  exact (P.solution_iff E v).mp hv

/-- Exact intrinsic existence-and-uniqueness theorem over the regular
coefficient ring. -/
theorem existsUnique_intrinsicSolution :
    ∃! v : V, P.evaluate v = P.rhs := by
  refine ⟨P.intrinsicSolution E Hrank Haug,
    P.intrinsicSolution_solves E Hrank Haug, ?_⟩
  intro v hv
  exact P.solution_eq_intrinsicSolution E Hrank Haug hv

end Packet

end

end ConormalAffinePacketOverRing
end Experimental
end PCRLean
