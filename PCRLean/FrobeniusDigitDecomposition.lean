import Mathlib
import PCRLean.FrobeniusPowerIdeal
import PCRLean.IdealEndomorphismDescent

/-!
# Frobenius digit decomposition

A finite free Frobenius frame and a root equivalence turn ordinary module
coordinates into Frobenius digits.  Every ambient element has a unique finite
expansion

`f = Σ_i (root(coeff_i f))^(p^e) * v_i`,

where `v_i` are the Frobenius-frame basis vectors.  In a polynomial `p`-basis,
these vectors are the monomials whose exponents are the first base-`p` digits.
Iterating the construction yields a finite Frobenius digit tree.

This is the representation-theoretic bridge behind recursive coefficient
extraction: positive digits lower marked order, while the zero digit descends
to the Frobenius base.
-/

namespace PCRLean
namespace FrobeniusDigitDecomposition

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {ι : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]
variable (p e : Nat) [ExpChar A p]

/-- Root of one Frobenius-frame coefficient. -/
def rootCoefficient
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    (f : A) (i : ι) : A :=
  S.rootEquiv (F.coord f i)

/-- The structural base coefficient is the `p^e`-th power of its root digit. -/
theorem algebraMap_coefficient_eq_root_pow
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    (f : A) (i : ι) :
    algebraMap R A (F.coord f i) =
      (rootCoefficient p e F S f i) ^ (p ^ e) := by
  rw [S.algebraMap_eq]
  rfl

/-- Every element has an exact finite Frobenius digit expansion. -/
theorem reconstruct
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    (f : A) :
    f = ∑ i : ι,
      (rootCoefficient p e F S f i) ^ (p ^ e) *
        F.basisVector i := by
  calc
    f = ∑ i : ι, F.coord f i • F.basisVector i :=
      (IdealEndomorphismDescent.UnitFrame.reconstruct F f).symm
    _ = ∑ i : ι,
        algebraMap R A (F.coord f i) * F.basisVector i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Algebra.smul_def]
    _ = ∑ i : ι,
        (rootCoefficient p e F S f i) ^ (p ^ e) *
          F.basisVector i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [algebraMap_coefficient_eq_root_pow p e F S f i]

/-- The Frobenius digits are unique because the coordinate frame is an
equivalence. -/
theorem rootCoefficient_injective
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    {f g : A}
    (h : ∀ i, rootCoefficient p e F S f i =
      rootCoefficient p e F S g i) :
    f = g := by
  apply F.coord.injective
  funext i
  apply S.rootEquiv.injective
  exact h i

/-- Coordinatewise membership in a base ideal gives a digit expansion whose
roots all lie in the corresponding actual root ideal. -/
theorem rootCoefficient_mem_rootIdeal
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    (J : Ideal R) {f : A}
    (hcoeff : ∀ i, F.coord f i ∈ J) (i : ι) :
    rootCoefficient p e F S f i ∈ S.rootIdeal J := by
  exact Ideal.mem_map_of_mem S.rootEquiv.toRingHom (hcoeff i)

/-- Finite packet form of the digit decomposition for elements whose
coordinates belong to a fixed base ideal. -/
theorem exists_finite_root_digits
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (S : FrobeniusPowerIdeal.RootEquiv (A := A) p e (R := R))
    (J : Ideal R) {f : A}
    (hcoeff : ∀ i, F.coord f i ∈ J) :
    ∃ digits : ι → A,
      (∀ i, digits i ∈ S.rootIdeal J) ∧
      f = ∑ i : ι,
        (digits i) ^ (p ^ e) * F.basisVector i := by
  exact ⟨fun i => rootCoefficient p e F S f i,
    rootCoefficient_mem_rootIdeal p e F S J hcoeff,
    reconstruct p e F S f⟩

end

end FrobeniusDigitDecomposition
end PCRLean
