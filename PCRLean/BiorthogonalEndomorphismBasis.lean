import Mathlib
import PCRLean.EndomorphismGeneration

/-!
# Biorthogonal frames generate the full endomorphism algebra

A complete dual frame consists of vectors and coefficient functionals with the
usual reconstruction identity.  Its rank-one operators become the coordinate
matrix units after conjugation by the coefficient map.  Thus stability under
these finitely many rank-one operators forces full endomorphism invariance and,
for ideals in a unit-normalized algebra frame, descent from the base ring.

In a local Frobenius chart the vectors are the finite Frobenius monomial basis
and the functionals are Cartier/Hasse coefficient extractors.  The remaining
geometric task is to identify those concrete coefficient extractors and their
rank-one composites inside the chosen transformed operator packet.
-/

namespace PCRLean
namespace BiorthogonalEndomorphismBasis

noncomputable section

universe u v w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [DecidableEq ι]

/-- A finite complete dual frame.  Reconstruction is included as an explicit
certificate, so no freeness or projectivity instance must be inferred. -/
structure Frame where
  vector : ι → M
  functional : ι → (M →ₗ[R] R)
  biorthogonal :
    ∀ i j, functional i (vector j) = if i = j then 1 else 0
  reconstruct :
    ∀ x, x = ∑ i, functional i x • vector i

namespace Frame

variable (F : Frame (R := R) (M := M) (ι := ι))

/-- Coordinate evaluation by the dual frame. -/
def evaluate : M →ₗ[R] (ι → R) where
  toFun x i := F.functional i x
  map_add' := by
    intro x y
    funext i
    exact map_add (F.functional i) x y
  map_smul' := by
    intro r x
    funext i
    exact map_smul (F.functional i) r x

/-- Synthesis from the frame vectors. -/
def synthesize : (ι → R) →ₗ[R] M where
  toFun a := ∑ i, a i • F.vector i
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp [Finset.smul_sum, mul_smul]

/-- Synthesis after evaluation is the identity. -/
theorem synthesize_evaluate (x : M) :
    F.synthesize (F.evaluate x) = x := by
  exact (F.reconstruct x).symm

/-- Evaluation after synthesis is the identity. -/
theorem evaluate_synthesize (a : ι → R) :
    F.evaluate (F.synthesize a) = a := by
  funext i
  simp [evaluate, synthesize, F.biorthogonal]

/-- The coefficient map is a linear equivalence. -/
def coordinateEquiv : M ≃ₗ[R] (ι → R) where
  toFun := F.evaluate
  invFun := F.synthesize
  left_inv := F.synthesize_evaluate
  right_inv := F.evaluate_synthesize
  map_add' := F.evaluate.map_add
  map_smul' := F.evaluate.map_smul

@[simp] theorem coordinateEquiv_apply (x : M) :
    F.coordinateEquiv x = F.evaluate x := rfl

@[simp] theorem coordinateEquiv_symm_apply (a : ι → R) :
    F.coordinateEquiv.symm a = F.synthesize a := rfl

/-- The rank-one operator sending the `j`-th coefficient to the `i`-th frame
vector. -/
def rankOne (i j : ι) : Module.End R M where
  toFun x := F.functional j x • F.vector i
  map_add' := by
    intro x y
    simp [add_smul]
  map_smul' := by
    intro r x
    simp [mul_smul]

@[simp] theorem rankOne_apply (i j : ι) (x : M) :
    F.rankOne i j x = F.functional j x • F.vector i := rfl

/-- Under coefficient coordinates, rank-one frame operators are exactly the
standard matrix units. -/
theorem conjugate_rankOne_eq_matrixUnit (i j : ι) :
    EndomorphismGeneration.conjugateToCoordinates
        F.coordinateEquiv (F.rankOne i j) =
      MatrixStableSubmodule.matrixUnit (R := R) i j := by
  ext a k
  by_cases hki : k = i
  · subst k
    simp [EndomorphismGeneration.conjugateToCoordinates,
      coordinateEquiv, evaluate, synthesize, rankOne,
      F.biorthogonal]
  · simp [EndomorphismGeneration.conjugateToCoordinates,
      coordinateEquiv, evaluate, synthesize, rankOne,
      F.biorthogonal, hki]

/-- The finite family of all rank-one frame operators. -/
def rankOnePacket : (ι × ι) → Module.End R M :=
  fun ij => F.rankOne ij.1 ij.2

/-- The conjugated rank-one packet generates every coordinate matrix unit. -/
theorem conjugated_rankOnePacket_generatesMatrixUnits :
    EndomorphismGeneration.GeneratesMatrixUnits
      (fun ij => EndomorphismGeneration.conjugateToCoordinates
        F.coordinateEquiv (F.rankOnePacket ij)) := by
  intro i j
  have hgen := EndomorphismGeneration.Generated.generator
    (ops := fun ij => EndomorphismGeneration.conjugateToCoordinates
      F.coordinateEquiv (F.rankOnePacket ij)) (i, j)
  simpa [rankOnePacket, F.conjugate_rankOne_eq_matrixUnit i j] using hgen

/-- A frame vector equal to the algebra unit turns the coefficient equivalence
into the unit-normalized frame required by ideal descent. -/
def unitFrame {A : Type*} [CommRing A] [Algebra R A]
    (F : Frame (R := R) (M := A) (ι := ι))
    (i₀ : ι) (hunit : F.vector i₀ = 1) :
    IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι) where
  coord := F.coordinateEquiv
  unitIndex := i₀
  coord_one := by
    ext j
    change F.functional j 1 = Pi.single i₀ 1 j
    rw [← hunit]
    by_cases hji : j = i₀
    · subst j
      simp [F.biorthogonal]
    · simp [F.biorthogonal, hji]

section Ideal

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Stability under the complete finite rank-one packet forces an ideal to be
extended from the base ring. -/
theorem ideal_eq_map_comap_of_rankOne_stable
    (F : Frame (R := R) (M := A) (ι := ι))
    (i₀ : ι) (hunit : F.vector i₀ = 1)
    (I : Ideal A)
    (hstable : ∀ ij,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (F.rankOnePacket ij)) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply EndomorphismGeneration.ideal_eq_map_comap_of_generated_matrixUnits
    (F.unitFrame i₀ hunit) F.rankOnePacket I
  · simpa [unitFrame] using F.conjugated_rankOnePacket_generatesMatrixUnits
  · exact hstable

end Ideal

end Frame

end

end BiorthogonalEndomorphismBasis
end PCRLean
