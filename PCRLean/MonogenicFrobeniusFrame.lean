import Mathlib
import PCRLean.IdealOperatorPacketDescent

/-!
# Monogenic Frobenius frames

A monogenic finite free algebra frame consists of a generator `x`, a coordinate
basis `1,x,...,x^(q-1)`, and the relation `x^q = t` from the base ring.  On such
a frame, the coordinate multiplication operators of `FiniteHasseModel` are not
merely abstract linear maps: after transport to the algebra they are exactly
multiplication by the powers of `x`.

Consequently ideal stability under the multiplication half of the primitive
packet is automatic.  The only substantive stability hypothesis needed for
Frobenius-base ideal descent is stability under the finite transported Hasse
operators.  This file discharges the multiplication-realization hypothesis in
`IdealOperatorPacketDescent` and also constructs the frame canonically from a
power basis satisfying a monogenic relation.
-/

namespace PCRLean
namespace MonogenicFrobeniusFrame

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- A unit-normalized monogenic coordinate frame with relation `gen^q = t`. -/
structure Frame (q : Nat) (t : R) where
  q_pos : 0 < q
  gen : A
  coord : A ≃ₗ[R] (Fin q → R)
  coord_symm_basis : ∀ i : Fin q,
    coord.symm (FiniteHasseModel.basisVector (R := R) q i) = gen ^ i.1
  relation : gen ^ q = algebraMap R A t

namespace Frame

variable {q : Nat} {t : R}
variable (F : Frame (R := R) (A := A) q t)

/-- The actual algebra vector corresponding to one monomial coordinate. -/
def frameVector (i : Fin q) : A :=
  F.coord.symm (FiniteHasseModel.basisVector (R := R) q i)

@[simp] theorem frameVector_eq_pow (i : Fin q) :
    F.frameVector i = F.gen ^ i.1 :=
  F.coord_symm_basis i

/-- The coordinate index of the algebra unit. -/
def unitIndex : Fin q := ⟨0, F.q_pos⟩

/-- A monogenic frame is a unit-normalized finite free frame. -/
def unitFrame :
    IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := Fin q) where
  coord := F.coord
  unitIndex := F.unitIndex
  coord_one := by
    apply F.coord.symm.injective
    rw [F.coord.symm_apply_apply]
    calc
      (1 : A) = F.gen ^ 0 := by simp
      _ = F.frameVector F.unitIndex :=
        (F.frameVector_eq_pow F.unitIndex).symm
      _ = F.coord.symm (Pi.single F.unitIndex 1) := by
        rfl

/-- The wrapped multiplication formula in the finite coordinate model. -/
theorem finiteMultiply_basis_of_ge
    (a c : Fin q) (hge : q ≤ a.1 + c.1) :
    FiniteHasseModel.multiply (R := R) q t a
        (FiniteHasseModel.basisVector (R := R) q c) =
      t • FiniteHasseModel.basisVector (R := R) q
        ⟨a.1 + c.1 - q, by omega⟩ := by
  simp [FiniteHasseModel.multiply, FiniteHasseModel.multiplyImage,
    Nat.not_lt.mpr hge]

/-- On every monomial basis vector, transported coordinate multiplication is
actual multiplication by the corresponding power of the generator. -/
theorem pullback_multiply_basis
    (a c : Fin q) :
    CoordinatePacketDescent.pullbackOperator F.coord
        (FiniteHasseModel.multiply (R := R) q t a)
        (F.frameVector c) =
      IdealOperatorPacketDescent.leftMultiplication
        (R := R) (F.gen ^ a.1) (F.frameVector c) := by
  by_cases hlt : a.1 + c.1 < q
  · let d : Fin q := ⟨a.1 + c.1, hlt⟩
    calc
      CoordinatePacketDescent.pullbackOperator F.coord
          (FiniteHasseModel.multiply (R := R) q t a)
          (F.frameVector c) = F.frameVector d := by
        apply F.coord.injective
        rw [CoordinatePacketDescent.pullbackOperator_apply]
        simpa [frameVector] using
          (FiniteHasseModel.multiply_basis_of_lt
            (R := R) q t a c hlt)
      _ = F.gen ^ (a.1 + c.1) := by
        simpa [d] using F.frameVector_eq_pow d
      _ = F.gen ^ a.1 * F.gen ^ c.1 := by
        rw [pow_add]
      _ = IdealOperatorPacketDescent.leftMultiplication
          (R := R) (F.gen ^ a.1) (F.frameVector c) := by
        rw [IdealOperatorPacketDescent.leftMultiplication_apply,
          F.frameVector_eq_pow c]
  · have hge : q ≤ a.1 + c.1 := Nat.le_of_not_gt hlt
    let d : Fin q := ⟨a.1 + c.1 - q, by omega⟩
    calc
      CoordinatePacketDescent.pullbackOperator F.coord
          (FiniteHasseModel.multiply (R := R) q t a)
          (F.frameVector c) = t • F.frameVector d := by
        apply F.coord.injective
        rw [CoordinatePacketDescent.pullbackOperator_apply]
        simpa [frameVector] using
          (finiteMultiply_basis_of_ge
            (R := R) (q := q) (t := t) a c hge)
      _ = algebraMap R A t * F.gen ^ d.1 := by
        rw [F.frameVector_eq_pow d, Algebra.smul_def]
      _ = F.gen ^ q * F.gen ^ d.1 := by
        rw [F.relation]
      _ = F.gen ^ (q + d.1) := by
        rw [pow_add]
      _ = F.gen ^ (a.1 + c.1) := by
        rw [show q + d.1 = a.1 + c.1 by
          simp [d, Nat.add_sub_of_le hge]]
      _ = F.gen ^ a.1 * F.gen ^ c.1 := by
        rw [pow_add]
      _ = IdealOperatorPacketDescent.leftMultiplication
          (R := R) (F.gen ^ a.1) (F.frameVector c) := by
        rw [IdealOperatorPacketDescent.leftMultiplication_apply,
          F.frameVector_eq_pow c]

/-- Transported coordinate multiplication equals actual algebra multiplication
on the whole finite free module. -/
theorem pullback_multiply_eq_leftMultiplication (a : Fin q) :
    CoordinatePacketDescent.pullbackOperator F.coord
        (FiniteHasseModel.multiply (R := R) q t a) =
      IdealOperatorPacketDescent.leftMultiplication
        (R := R) (F.gen ^ a.1) := by
  apply LinearMap.ext
  intro x
  rw [IdealEndomorphismDescent.UnitFrame.reconstruct F.unitFrame x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c hc
  have hb := F.pullback_multiply_basis a c
  simpa [unitFrame, IdealEndomorphismDescent.UnitFrame.basisVector,
    frameVector, FiniteHasseModel.basisVector] using
      congrArg (fun y : A => F.coord x c • y) hb

/-- Hasse-only ideal descent on an actual monogenic algebra frame. -/
theorem ideal_eq_map_comap_of_hasse_stable
    (I : Ideal A)
    (hhasse : ∀ d : Fin q,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator F.coord
          (FiniteHasseModel.hasse (R := R) q d))) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  exact IdealOperatorPacketDescent.ideal_eq_map_comap_of_hasse_stable
    (R := R) (A := A) q t F.unitFrame I
    (fun m => ⟨F.gen ^ m.1,
      F.pullback_multiply_eq_leftMultiplication m⟩)
    hhasse

end Frame

/-- Every power basis whose top power lies in the base ring determines a
monogenic Frobenius frame. -/
def ofPowerBasis [Nontrivial A]
    (pb : PowerBasis R A) (t : R)
    (hrelation : pb.gen ^ pb.dim = algebraMap R A t) :
    Frame (R := R) (A := A) pb.dim t where
  q_pos := pb.dim_pos
  gen := pb.gen
  coord := pb.basis.equivFun
  coord_symm_basis := by
    intro i
    calc
      pb.basis.equivFun.symm
          (FiniteHasseModel.basisVector (R := R) pb.dim i) =
        pb.basis i := by
          apply pb.basis.equivFun.injective
          simp [FiniteHasseModel.basisVector]
      _ = pb.gen ^ i.1 := pb.basis_eq_pow i
  relation := hrelation

/-- Power-basis form of Hasse-only Frobenius ideal descent. -/
theorem ideal_eq_map_comap_of_powerBasis_hasse_stable
    [Nontrivial A]
    (pb : PowerBasis R A) (t : R)
    (hrelation : pb.gen ^ pb.dim = algebraMap R A t)
    (I : Ideal A)
    (hhasse : ∀ d : Fin pb.dim,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator pb.basis.equivFun
          (FiniteHasseModel.hasse (R := R) pb.dim d))) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  exact (ofPowerBasis (R := R) (A := A) pb t hrelation).ideal_eq_map_comap_of_hasse_stable
    I hhasse

end

end MonogenicFrobeniusFrame
end PCRLean
