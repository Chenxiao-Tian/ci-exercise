import Mathlib
import PCRLean.FunctionalPacketIdeal
import PCRLean.LinearPacketIdeal

/-!
# Polynomial coordinate changes from a full dual frame

A full family of linear functionals together with a biorthogonal reconstruction
frame defines a linear automorphism of affine space and hence an algebra
automorphism of its polynomial ring. Under this automorphism the packet linear
forms are ordinary coordinate variables.

This is the algebraic regularity bridge for full-rank linear packets. A
constant-rank packet is reduced to this situation after adjoining a basis of
its persistent kernel.
-/

namespace PCRLean
namespace LinearCoordinateChange

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]

abbrev Direction := σ → K
abbrev Dual := (σ → K) →ₗ[K] K

/-- A full dual frame with explicit reconstruction of every direction vector. -/
structure FullFrame where
  functional : σ → Dual (K := K) (σ := σ)
  vector : σ → Direction (K := K) (σ := σ)
  biorthogonal : ∀ i j : σ,
    functional i (vector j) = if i = j then 1 else 0
  reconstruct : ∀ (x : Direction (K := K) (σ := σ)) (i : σ),
    x i = ∑ j : σ, functional j x * vector j i

namespace FullFrame

variable (F : FullFrame (K := K) (σ := σ))

/-- Every vector in the coordinate direction space is the sum of its standard
coordinate components. -/
theorem sum_coord_smul_basisVector
    (x : Direction (K := K) (σ := σ)) :
    (∑ i : σ, x i •
      FunctionalPacketIdeal.basisVector (K := K) (σ := σ) i) = x := by
  classical
  funext j
  simp [FunctionalPacketIdeal.basisVector]

/-- Evaluation of a functional can be recovered from its standard coordinate
row. -/
theorem functional_coordinate_expansion
    (f : Dual (K := K) (σ := σ))
    (x : Direction (K := K) (σ := σ)) :
    ∑ i : σ,
        f (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) i) * x i =
      f x := by
  have h := congrArg f (sum_coord_smul_basisVector (K := K) (σ := σ) x)
  simpa [map_sum, map_smul, mul_comm] using h

/-- Linear form corresponding to the `i`th new coordinate. -/
def forwardVariable (i : σ) : MvPolynomial σ K :=
  FunctionalPacketIdeal.functionalPolynomial
    (K := K) (σ := σ) (F.functional i)

/-- Linear form expressing the old `i`th coordinate in the new frame. -/
def inverseVariable (i : σ) : MvPolynomial σ K :=
  LinearPacketIdeal.linearPolynomial (fun j => F.vector j i)

/-- Forward polynomial substitution. -/
def forward : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval F.forwardVariable

/-- Inverse polynomial substitution. -/
def inverse : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval F.inverseVariable

@[simp] theorem forward_X (i : σ) :
    F.forward (MvPolynomial.X i) = F.forwardVariable i := by
  simp [forward]

@[simp] theorem inverse_X (i : σ) :
    F.inverse (MvPolynomial.X i) = F.inverseVariable i := by
  simp [inverse]

/-- Applying the inverse substitution to a packet linear form gives the
corresponding ordinary coordinate. -/
theorem inverse_forwardVariable (i : σ) :
    F.inverse (F.forwardVariable i) = MvPolynomial.X i := by
  classical
  have hrow : ∀ j : σ,
      ∑ x : σ,
        F.functional i
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x) *
          F.vector j x =
        if i = j then 1 else 0 := by
    intro j
    calc
      ∑ x : σ,
          F.functional i
              (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x) *
            F.vector j x =
          F.functional i (F.vector j) :=
        functional_coordinate_expansion
          (K := K) (σ := σ) (F.functional i) (F.vector j)
      _ = if i = j then 1 else 0 := F.biorthogonal i j
  rw [forwardVariable, FunctionalPacketIdeal.functionalPolynomial,
    LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, MvPolynomial.map_C,
    inverse_X, inverseVariable, LinearPacketIdeal.linearPolynomial]
  calc
    (∑ x : σ,
        MvPolynomial.C
            (F.functional i
              (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x)) *
          ∑ j : σ, MvPolynomial.C (F.vector j x) * MvPolynomial.X j) =
      ∑ j : σ,
        MvPolynomial.C
            (∑ x : σ,
              F.functional i
                  (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x) *
                F.vector j x) *
          MvPolynomial.X j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [map_mul]
    _ = MvPolynomial.X i := by
      simp_rw [hrow]
      simp

/-- Applying the forward substitution to an inverse coordinate form gives the
original coordinate. -/
theorem forward_inverseVariable (i : σ) :
    F.forward (F.inverseVariable i) = MvPolynomial.X i := by
  classical
  have hrow : ∀ j : σ,
      ∑ x : σ,
        F.vector x i *
          F.functional x
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j) =
        if j = i then 1 else 0 := by
    intro j
    have h := F.reconstruct
      (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j) i
    simpa [FunctionalPacketIdeal.basisVector, mul_comm] using h
  rw [inverseVariable, LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, MvPolynomial.map_C,
    forward_X, forwardVariable,
    FunctionalPacketIdeal.functionalPolynomial,
    LinearPacketIdeal.linearPolynomial]
  calc
    (∑ x : σ, MvPolynomial.C (F.vector x i) *
        ∑ j : σ,
          MvPolynomial.C
              (F.functional x
                (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j)) *
            MvPolynomial.X j) =
      ∑ j : σ,
        MvPolynomial.C
            (∑ x : σ,
              F.vector x i *
                F.functional x
                  (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j)) *
          MvPolynomial.X j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [map_mul]
    _ = MvPolynomial.X i := by
      simp_rw [hrow]
      simp

/-- Inverse after forward is the identity algebra homomorphism. -/
theorem inverse_comp_forward :
    F.inverse.comp F.forward = AlgHom.id K (MvPolynomial σ K) := by
  ext i
  simp [F.inverse_forwardVariable]

/-- Forward after inverse is the identity algebra homomorphism. -/
theorem forward_comp_inverse :
    F.forward.comp F.inverse = AlgHom.id K (MvPolynomial σ K) := by
  ext i
  simp [F.forward_inverseVariable]

/-- The resulting polynomial algebra equivalence. -/
noncomputable def polynomialEquiv :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom F.forward F.inverse
    F.forward_comp_inverse F.inverse_comp_forward

/-- The automorphism sends ordinary coordinates to the packet forms. -/
@[simp] theorem polynomialEquiv_X (i : σ) :
    F.polynomialEquiv (MvPolynomial.X i) = F.forwardVariable i := by
  simp [polynomialEquiv]

end FullFrame

end

end LinearCoordinateChange
end PCRLean
