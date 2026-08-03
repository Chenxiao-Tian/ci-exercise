import Mathlib
import PCRLean.CoordinatePacketDescent
import PCRLean.FiniteHasseModel

/-!
# Ideal descent from a partitioned operator packet

For ideals, stability under multiplication operators is automatic once those
operators are realized as actual ring multiplication. Hence a coordinate packet
may be partitioned into multiplication operators and genuinely differential
operators. If the combined packet generates all matrix units, only stability
under the differential part remains as a substantive hypothesis.

Applied to the finite monogenic Frobenius frame, this reduces Frobenius-base
ideal descent to stability under the finite Hasse packet together with the
chart-level identification of coordinate multiplication with multiplication in
the actual algebra.
-/

namespace PCRLean
namespace IdealOperatorPacketDescent

noncomputable section

universe u v w x y

variable {R : Type u} {A : Type v} {ι : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R

/-- Multiplication by an element of the actual algebra, regarded as an
`R`-linear endomorphism. -/
def leftMultiplication (a : A) : Module.End R A where
  toFun x := a * x
  map_add' := by
    intro x y
    exact mul_add a x y
  map_smul' := by
    intro r x
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem leftMultiplication_apply (a x : A) :
    leftMultiplication (R := R) a x = a * x := rfl

/-- Every ideal is stable under every actual multiplication endomorphism. -/
theorem leftMultiplication_stable (I : Ideal A) (a : A) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R) I)
      (leftMultiplication (R := R) a) := by
  intro x hx
  change a * x ∈ I
  exact I.mul_mem_left a hx

/-- A coordinate packet partitioned into multiplication and differential
operators. -/
def partitionedPacket
    {μ : Type x} {δ : Type y}
    (mulOps : μ → Module.End R (Coordinates (R := R) (ι := ι)))
    (diffOps : δ → Module.End R (Coordinates (R := R) (ι := ι))) :
    (μ ⊕ δ) → Module.End R (Coordinates (R := R) (ι := ι))
  | Sum.inl m => mulOps m
  | Sum.inr d => diffOps d

/-- Main partitioned descent theorem. The multiplication half needs only an
actual multiplication realization; stability is then supplied by the ideal
axioms. -/
theorem ideal_eq_map_comap_of_partitionedPacket
    {μ : Type x} {δ : Type y}
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (mulOps : μ → Module.End R (Coordinates (R := R) (ι := ι)))
    (diffOps : δ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits
      (partitionedPacket mulOps diffOps))
    (I : Ideal A)
    (hmul : ∀ m, ∃ a : A,
      CoordinatePacketDescent.pullbackOperator F.coord (mulOps m) =
        leftMultiplication (R := R) a)
    (hdiff : ∀ d,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator F.coord (diffOps d))) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply CoordinatePacketDescent.ideal_eq_map_comap_of_pullbackPacket_stable
    F (partitionedPacket mulOps diffOps) hgen I
  intro k
  cases k with
  | inl m =>
      change EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator F.coord (mulOps m))
      rcases hmul m with ⟨a, ha⟩
      rw [ha]
      exact leftMultiplication_stable (R := R) I a
  | inr d =>
      change EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator F.coord (diffOps d))
      exact hdiff d

section FiniteHasse

variable (q : ℕ)

/-- The finite monogenic primitive packet is exactly the partition into
coordinate multiplication and Hasse operators. -/
theorem partitionedPacket_eq_primitivePacket (t : R) :
    partitionedPacket
      (FiniteHasseModel.multiply (R := R) q t)
      (FiniteHasseModel.hasse (R := R) q) =
        FiniteHasseModel.primitivePacket (R := R) q t := by
  funext k
  cases k <;> rfl

/-- On a finite monogenic Frobenius frame, an ideal descends once coordinate
multiplication is identified with actual ring multiplication and the ideal is
stable under the finite Hasse operators. -/
theorem ideal_eq_map_comap_of_hasse_stable
    (t : R)
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := Fin q))
    (I : Ideal A)
    (hmul : ∀ m, ∃ a : A,
      CoordinatePacketDescent.pullbackOperator F.coord
          (FiniteHasseModel.multiply (R := R) q t m) =
        leftMultiplication (R := R) a)
    (hhasse : ∀ d,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator F.coord
          (FiniteHasseModel.hasse (R := R) q d))) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply ideal_eq_map_comap_of_partitionedPacket
    F
    (FiniteHasseModel.multiply (R := R) q t)
    (FiniteHasseModel.hasse (R := R) q)
    ?_ I hmul hhasse
  rw [partitionedPacket_eq_primitivePacket (R := R) q t]
  exact FiniteHasseModel.primitivePacket_generatesMatrixUnits
    (R := R) q t

end FiniteHasse

end

end IdealOperatorPacketDescent
end PCRLean
