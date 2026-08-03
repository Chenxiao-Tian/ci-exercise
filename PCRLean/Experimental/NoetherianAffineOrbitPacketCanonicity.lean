import Mathlib
import PCRLean.Experimental.NoetherianAffineOrbitPacket

/-!
# Canonicity of Noetherian affine orbit determinants

Different finite raw packets may span the same Noetherian operator orbit.  The
previous affine-orbit theorem shows that their finite equation systems have the
same solution predicate.  This file lifts that statement through the exact
maximal-minor range criterion.

Assuming the coordinate matrices of two finite packets both satisfy the
maximal-minor cover condition:

* augmented-minor consistency for one packet is equivalent to consistency for
  the other;
* the two determinantal coordinate solutions pull back to the same intrinsic
  vector; and
* that vector is the unique solution of the complete infinite affine orbit.

Thus neither Noetherian generator choice nor coordinate choice remains in the
resulting centre solution, within the represented full-rank chamber.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianAffineOrbitPacketCanonicity

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable [IsNoetherianRing K] [IsRegularRing K]
variable {D : Type v} {T : Type w} {Op : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup T] [Module K T]
variable [IsNoetherian K D]
variable [FiniteDimensional K T]
variable {σ : Type y} [Fintype σ] [DecidableEq σ] [Nonempty σ]

variable {ops : Op → Module.End K D} {seed : D}
variable {pair : D →ₗ[K] Module.Dual K T}
variable {value : D →ₗ[K] K}

open NoetherianAffineOrbitPacket

variable
  (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
variable (Frame : T ≃ₗ[K] (σ → K))

abbrev finiteC := finitePacket (value := value) C
abbrev finiteE := finitePacket (value := value) E

variable
  (HC : MaximalMinorAtlas.FullRankCover ((finiteC C).matrix Frame))
  (HE : MaximalMinorAtlas.FullRankCover ((finiteE E).matrix Frame))

/-- Coordinate solution existence for the first packet is equivalent to the
full infinite-orbit solution predicate. -/
theorem C_exists_solution_iff_orbit :
    (∃ z : σ → K,
      ((finiteC C).matrix Frame).mulVec z = (finiteC C).rhs) ↔
      ∃ x : T,
        OrbitSolution (ops := ops) (seed := seed)
          (pair := pair) (value := value) x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Frame.symm z, ?_⟩
    apply (C.finitePacket_solution_iff_orbitSolution
      (value := value) (Frame.symm z)).mp
    exact ((finiteC C).coordinate_solution_iff Frame z).mpr hz
  · rintro ⟨x, hx⟩
    refine ⟨Frame x, ?_⟩
    apply ((finiteC C).solution_iff Frame x).mp
    exact (C.finitePacket_solution_iff_orbitSolution
      (value := value) x).mpr hx

/-- The analogous equivalence for the second packet. -/
theorem E_exists_solution_iff_orbit :
    (∃ z : σ → K,
      ((finiteE E).matrix Frame).mulVec z = (finiteE E).rhs) ↔
      ∃ x : T,
        OrbitSolution (ops := ops) (seed := seed)
          (pair := pair) (value := value) x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Frame.symm z, ?_⟩
    apply (E.finitePacket_solution_iff_orbitSolution
      (value := value) (Frame.symm z)).mp
    exact ((finiteE E).coordinate_solution_iff Frame z).mpr hz
  · rintro ⟨x, hx⟩
    refine ⟨Frame x, ?_⟩
    apply ((finiteE E).solution_iff Frame x).mp
    exact (E.finitePacket_solution_iff_orbitSolution
      (value := value) x).mpr hx

/-- Augmented-minor consistency is independent of the finite Noetherian packet
choice. -/
theorem augmentedRankCondition_iff :
    MaximalMinorAugmentedPacket.AugmentedRankCondition
        ((finiteC C).matrix Frame) (finiteC C).rhs ↔
      MaximalMinorAugmentedPacket.AugmentedRankCondition
        ((finiteE E).matrix Frame) (finiteE E).rhs := by
  rw [MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        ((finiteC C).matrix Frame) (finiteC C).rhs HC,
      MaximalMinorRangeCriterion.augmentedRankCondition_iff_exists_solution
        ((finiteE E).matrix Frame) (finiteE E).rhs HE,
      C_exists_solution_iff_orbit C Frame,
      E_exists_solution_iff_orbit E Frame]

/-- Transport a determinantal certificate between finite orbit packets. -/
noncomputable def transportAugmented
    (HaugC : MaximalMinorAugmentedPacket.AugmentedRankCondition
      ((finiteC C).matrix Frame) (finiteC C).rhs) :
    MaximalMinorAugmentedPacket.AugmentedRankCondition
      ((finiteE E).matrix Frame) (finiteE E).rhs :=
  (augmentedRankCondition_iff C E Frame HC HE).mp HaugC

/-- Both finite packets recover the same intrinsic infinite-orbit solution. -/
theorem intrinsicSolution_eq
    (HaugC : MaximalMinorAugmentedPacket.AugmentedRankCondition
      ((finiteC C).matrix Frame) (finiteC C).rhs) :
    (finiteC C).intrinsicSolution Frame HC HaugC =
      (finiteE E).intrinsicSolution Frame HE
        (transportAugmented C E Frame HC HE HaugC) := by
  apply (finiteC C).solution_eq_intrinsicSolution Frame HC HaugC
  apply (C.finitePacket_solution_iff_orbitSolution
    (value := value)
    ((finiteE E).intrinsicSolution Frame HE
      (transportAugmented C E Frame HC HE HaugC))).mpr
  apply (E.finitePacket_solution_iff_orbitSolution
    (value := value)
    ((finiteE E).intrinsicSolution Frame HE
      (transportAugmented C E Frame HC HE HaugC))).mp
  exact (finiteE E).intrinsicSolution_solves Frame HE
    (transportAugmented C E Frame HC HE HaugC)

end

end NoetherianAffineOrbitPacketCanonicity
end Experimental
end PCRLean
