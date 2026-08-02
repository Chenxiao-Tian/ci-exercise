import Mathlib
import PCRLean.FiniteFreeEndomorphismDescent

/-!
# Ideal descent from full finite-free endomorphism stability

Let `A` be a finite free algebra over a commutative base ring `R`.  Suppose a
chosen finite free frame contains the unit as one coordinate vector.  If an
ideal of `A`, viewed as an `R`-submodule, is invariant under every `R`-linear
endomorphism of `A`, then it is exactly the extension of its contraction to
`R`.

This is the abstract algebraic form of the finite-level Frobenius descent step:
a level-`e` differential ideal descends once the relevant differential
operators are identified with the full endomorphism algebra over the
Frobenius base and a local Frobenius frame containing `1` is supplied.
-/

namespace PCRLean
namespace IdealEndomorphismDescent

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {ι : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R

/-- An ideal of `A`, regarded only as an `R`-submodule. -/
def idealSubmodule (I : Ideal A) : Submodule R A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := by
    intro x y hx hy
    exact I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    change algebraMap R A r * x ∈ I
    exact I.mul_mem_left _ hx

@[simp] theorem mem_idealSubmodule (I : Ideal A) (x : A) :
    x ∈ idealSubmodule (R := R) I ↔ x ∈ I := Iff.rfl

/-- Full invariance of an ideal under the base-linear endomorphism algebra. -/
def FullyInvariant (I : Ideal A) : Prop :=
  FiniteFreeEndomorphismDescent.FullyInvariant
    (idealSubmodule (R := R) I)

/-- A finite free coordinate frame in which one coordinate vector is the
multiplicative unit. -/
structure UnitFrame where
  coord : A ≃ₗ[R] Coordinates (R := R) (ι := ι)
  unitIndex : ι
  coord_one : coord 1 = Pi.single unitIndex 1

namespace UnitFrame

variable (F : UnitFrame (R := R) (A := A) (ι := ι))

/-- The basis vector corresponding to one coordinate. -/
def basisVector (i : ι) : A :=
  F.coord.symm (Pi.single i 1)

@[simp] theorem coord_basisVector (i : ι) :
    F.coord (F.basisVector i) = Pi.single i 1 := by
  exact F.coord.apply_symm_apply _

/-- Scalar elements of the base have a single nonzero coordinate in the unit
slot. -/
theorem coord_algebraMap (r : R) :
    F.coord (algebraMap R A r) = Pi.single F.unitIndex r := by
  calc
    F.coord (algebraMap R A r) = F.coord (r • (1 : A)) := by
      simp [Algebra.smul_def]
    _ = r • F.coord 1 := F.coord.map_smul r 1
    _ = r • Pi.single F.unitIndex 1 := by rw [F.coord_one]
    _ = Pi.single F.unitIndex r := by
      ext j
      by_cases h : j = F.unitIndex
      · subst j
        simp
      · simp [h]

/-- The coefficient ideal attached to an ideal in the chosen frame. -/
def coefficientIdeal (I : Ideal A) : Ideal R :=
  MatrixStableSubmodule.coordinateIdeal
    ((idealSubmodule (R := R) I).map F.coord.toLinearMap)

/-- Full invariance survives passage to the coordinate module. -/
theorem mapped_fullyInvariant
    (I : Ideal A) (hI : FullyInvariant (R := R) I) :
    MatrixStableSubmodule.FullyInvariant
      ((idealSubmodule (R := R) I).map F.coord.toLinearMap) := by
  exact FiniteFreeEndomorphismDescent.map_fullyInvariant F.coord hI

/-- In a unit-normalized frame, the coefficient ideal is intrinsic: it is the
contraction of the original ideal to the base ring. -/
theorem coefficientIdeal_eq_comap
    (I : Ideal A) (hI : FullyInvariant (R := R) I) :
    F.coefficientIdeal I = I.comap (algebraMap R A) := by
  ext r
  constructor
  · intro hr
    have hi :=
      (MatrixStableSubmodule.mem_coordinateIdeal_iff
        ((idealSubmodule (R := R) I).map F.coord.toLinearMap) r).mp hr
        F.unitIndex
    rcases hi with ⟨x, hx, hxcoord⟩
    change algebraMap R A r ∈ I
    have hxeq : x = algebraMap R A r := by
      apply F.coord.injective
      calc
        F.coord x = Pi.single F.unitIndex r := hxcoord
        _ = F.coord (algebraMap R A r) := (F.coord_algebraMap r).symm
    simpa [hxeq] using hx
  · intro hr
    have hmap : F.coord (algebraMap R A r) ∈
        (idealSubmodule (R := R) I).map F.coord.toLinearMap := by
      exact ⟨algebraMap R A r, hr, rfl⟩
    have hc := MatrixStableSubmodule.coordinate_mem
      (F.mapped_fullyInvariant I hI) hmap F.unitIndex
    change r ∈ F.coefficientIdeal I
    simpa [coefficientIdeal, F.coord_algebraMap] using hc

/-- Exact membership criterion: a fully invariant ideal consists precisely of
vectors whose coordinates lie in its contraction to the base. -/
theorem mem_iff_coordinates_mem_comap
    (I : Ideal A) (hI : FullyInvariant (R := R) I) (x : A) :
    x ∈ I ↔ ∀ i, F.coord x i ∈ I.comap (algebraMap R A) := by
  have h := FiniteFreeEndomorphismDescent.mem_iff_coefficients_mem
    F.coord hI x
  rw [← F.coefficientIdeal_eq_comap I hI]
  exact h

/-- Reconstruction of a vector from its finite coordinate packet. -/
theorem reconstruct (x : A) :
    x = ∑ i, (F.coord x i) • F.basisVector i := by
  apply F.coord.injective
  rw [map_sum]
  simp only [map_smul, F.coord_basisVector]
  have hsum : (∑ i, Pi.single i (F.coord x i)) = F.coord x :=
    LinearMap.sum_single_apply (fun _ : ι => R) (F.coord x)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Main descent theorem: every ideal stable under the full base-linear
endomorphism algebra is extended from its contraction to the base. -/
theorem ideal_eq_map_comap_of_fullyInvariant
    (I : Ideal A) (hI : FullyInvariant (R := R) I) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply le_antisymm
  · intro x hx
    rw [F.reconstruct x]
    exact (I.comap (algebraMap R A)).map (algebraMap R A) |>.sum_mem
      (fun i _ => by
        have hc : F.coord x i ∈ I.comap (algebraMap R A) :=
          (F.mem_iff_coordinates_mem_comap I hI x).mp hx i
        have hscalar : algebraMap R A (F.coord x i) ∈
            (I.comap (algebraMap R A)).map (algebraMap R A) :=
          Ideal.mem_map_of_mem (algebraMap R A) hc
        change (F.coord x i) • F.basisVector i ∈
          (I.comap (algebraMap R A)).map (algebraMap R A)
        simpa [Algebra.smul_def] using
          ((I.comap (algebraMap R A)).map (algebraMap R A)).mul_mem_right
            (F.basisVector i) hscalar)
  · exact Ideal.map_comap_le

end UnitFrame

end

end IdealEndomorphismDescent
end PCRLean
