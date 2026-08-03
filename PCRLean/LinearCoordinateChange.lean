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

/-- Every coordinate vector is the finite sum of its standard-basis
coordinates. -/
theorem direction_eq_sum_basis
    (x : Direction (K := K) (σ := σ)) :
    x = ∑ i : σ, x i •
      FunctionalPacketIdeal.basisVector (K := K) (σ := σ) i := by
  classical
  funext j
  simp [FunctionalPacketIdeal.basisVector]

/-- Expanding a transverse frame vector in the standard basis converts
biorthogonality into the matrix row identity used by inverse substitution. -/
theorem functional_vector_row (i j : σ) :
    (∑ x : σ,
        F.functional i
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x) *
          F.vector j x) =
      if j = i then 1 else 0 := by
  classical
  have h := F.biorthogonal i j
  rw [F.direction_eq_sum_basis (F.vector j)] at h
  simp only [map_sum, map_smul] at h
  simpa [mul_comm, eq_comm] using h

/-- The reconstruction formula gives the complementary matrix row identity. -/
theorem vector_functional_row (i j : σ) :
    (∑ x : σ,
        F.vector x i *
          F.functional x
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j)) =
      if j = i then 1 else 0 := by
  classical
  have h := F.reconstruct
    (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j) i
  simpa [FunctionalPacketIdeal.basisVector, mul_comm, eq_comm] using h.symm

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

/-- Applying inverse substitution to a packet linear form gives the
corresponding ordinary coordinate. -/
theorem inverse_forwardVariable (i : σ) :
    F.inverse (F.forwardVariable i) = MvPolynomial.X i := by
  classical
  rw [forwardVariable, FunctionalPacketIdeal.functionalPolynomial,
    LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, inverse, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, inverseVariable]
  change
    (∑ x : σ,
        MvPolynomial.C
            (F.functional i
              (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x)) *
          LinearPacketIdeal.packetGenerator
            (fun x j : σ => F.vector j x) x) =
      MvPolynomial.X i
  rw [← LinearPacketIdeal.linearPolynomial_combination
    (packet := fun x j : σ => F.vector j x)
    (coeff := fun x =>
      F.functional i
        (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x))]
  have hrow :
      (fun j : σ => ∑ x : σ,
        F.functional i
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) x) *
          F.vector j x) =
        LinearPacketIdeal.coordinateRow (K := K) i := by
    funext j
    simpa [LinearPacketIdeal.coordinateRow] using
      F.functional_vector_row i j
  rw [hrow]
  exact LinearPacketIdeal.linearPolynomial_coordinateRow (K := K) i

/-- Applying forward substitution to an inverse coordinate form gives the
original coordinate. -/
theorem forward_inverseVariable (i : σ) :
    F.forward (F.inverseVariable i) = MvPolynomial.X i := by
  classical
  rw [inverseVariable, LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, forward, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, forwardVariable,
    FunctionalPacketIdeal.functionalPolynomial,
    FunctionalPacketIdeal.coefficientRow]
  change
    (∑ x : σ,
        MvPolynomial.C (F.vector x i) *
          LinearPacketIdeal.packetGenerator
            (fun x j : σ =>
              F.functional x
                (FunctionalPacketIdeal.basisVector
                  (K := K) (σ := σ) j)) x) =
      MvPolynomial.X i
  rw [← LinearPacketIdeal.linearPolynomial_combination
    (packet := fun x j : σ =>
      F.functional x
        (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j))
    (coeff := fun x => F.vector x i)]
  have hrow :
      (fun j : σ => ∑ x : σ,
        F.vector x i *
          F.functional x
            (FunctionalPacketIdeal.basisVector (K := K) (σ := σ) j)) =
        LinearPacketIdeal.coordinateRow (K := K) i := by
    funext j
    simpa [LinearPacketIdeal.coordinateRow] using
      F.vector_functional_row i j
  rw [hrow]
  exact LinearPacketIdeal.linearPolynomial_coordinateRow (K := K) i

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
