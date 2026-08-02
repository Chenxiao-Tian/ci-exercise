import Mathlib
import PCRLean.FunctionalPacketIdeal
import PCRLean.LinearPacketIdeal

/-!
# Polynomial coordinate changes from a full dual frame

A full family of linear functionals together with a biorthogonal reconstruction
frame defines a linear automorphism of affine space and hence an algebra
automorphism of its polynomial ring.  Under this automorphism the packet
linear forms are ordinary coordinate variables.

This is the algebraic regularity bridge for full-rank linear packets.  A
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
abbrev Dual := Module.Dual K Direction

/-- A full dual frame with explicit reconstruction of every direction vector. -/
structure FullFrame where
  functional : σ → Dual (K := K) (σ := σ)
  vector : σ → Direction (K := K) (σ := σ)
  biorthogonal : ∀ i j, functional i (vector j) = if i = j then 1 else 0
  reconstruct : ∀ x i, x i = ∑ j, functional j x * vector j i

namespace FullFrame

variable (F : FullFrame (K := K) (σ := σ))

/-- Linear form corresponding to the `i`th new coordinate. -/
def forwardVariable (i : σ) : MvPolynomial σ K :=
  FunctionalPacketIdeal.functionalPolynomial (F.functional i)

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
  rw [forwardVariable, FunctionalPacketIdeal.functionalPolynomial,
    LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, map_apply, MvPolynomial.map_C,
    inverse_X, inverseVariable]
  rw [Finset.sum_comm]
  apply MvPolynomial.induction_on
    (p := ∑ x, MvPolynomial.C
      (F.functional i (FunctionalPacketIdeal.basisVector (K := K) x)) *
      LinearPacketIdeal.linearPolynomial (fun j => F.vector j x))
    (fun n a => by simp)
    (fun p q hp hq => by simp [hp, hq])
  -- The preceding induction target is already linear; normalize directly.
  simp [LinearPacketIdeal.linearPolynomial,
    FunctionalPacketIdeal.basisVector]
  have hrow : ∀ j, ∑ x,
      F.functional i (FunctionalPacketIdeal.basisVector (K := K) x) *
        F.vector j x = if j = i then 1 else 0 := by
    intro j
    -- Apply the reconstruction identity to the standard basis vector.
    have h := F.reconstruct
      (FunctionalPacketIdeal.basisVector (K := K) i) j
    simpa [FunctionalPacketIdeal.basisVector, mul_comm] using h
  simp_rw [hrow]
  simp

/-- Applying the forward substitution to an inverse coordinate form gives the
original coordinate. -/
theorem forward_inverseVariable (i : σ) :
    F.forward (F.inverseVariable i) = MvPolynomial.X i := by
  classical
  rw [inverseVariable, LinearPacketIdeal.linearPolynomial]
  simp only [map_sum, map_mul, map_apply, MvPolynomial.map_C,
    forward_X, forwardVariable,
    FunctionalPacketIdeal.functionalPolynomial,
    LinearPacketIdeal.linearPolynomial]
  rw [Finset.sum_comm]
  have hrow : ∀ j, ∑ x, F.vector x i *
      F.functional x (FunctionalPacketIdeal.basisVector (K := K) j) =
        if j = i then 1 else 0 := by
    intro j
    have h := F.reconstruct
      (FunctionalPacketIdeal.basisVector (K := K) i) j
    simpa [FunctionalPacketIdeal.basisVector] using h
  simp_rw [hrow]
  simp

/-- Inverse after forward is the identity algebra homomorphism. -/
theorem inverse_comp_forward : F.inverse.comp F.forward = AlgHom.id K _ := by
  ext i
  simp [F.inverse_forwardVariable]

/-- Forward after inverse is the identity algebra homomorphism. -/
theorem forward_comp_inverse : F.forward.comp F.inverse = AlgHom.id K _ := by
  ext i
  simp [F.forward_inverseVariable]

/-- The resulting polynomial algebra equivalence. -/
def polynomialEquiv : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K where
  toAlgHom := F.forward
  invFun := F.inverse
  left_inv := by
    intro p
    have h := congrArg (fun H : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => H p)
      F.inverse_comp_forward
    simpa using h
  right_inv := by
    intro p
    have h := congrArg (fun H : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => H p)
      F.forward_comp_inverse
    simpa using h

/-- The automorphism sends ordinary coordinates to the packet forms. -/
@[simp] theorem polynomialEquiv_X (i : σ) :
    F.polynomialEquiv (MvPolynomial.X i) = F.forwardVariable i := by
  rfl

end FullFrame

end

end LinearCoordinateChange
end PCRLean
