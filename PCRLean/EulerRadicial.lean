import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.ReduceModChar

namespace PCRLean
namespace EulerRadicial

variable {R : Type*} {σ : Type*}
variable [CommRing R] [CharP R 2] [Fintype σ]

/-- In characteristic two, Euler's homogeneous identity for an odd degree
`2N+1` has coefficient one.  This is the algebraic core behind
`H = Σ xᵢ ∂ᵢH` in the nonprincipal radicial chambers. -/
theorem odd_euler_identity {H : MvPolynomial σ R} {N : Nat}
    (hH : H.IsHomogeneous (2 * N + 1)) :
    ∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i H = H := by
  rw [hH.sum_X_mul_pderiv]
  rw [nsmul_eq_mul]
  have hcast : ((2 * N + 1 : Nat) : MvPolynomial σ R) = 1 := by
    push_cast
    have htwo : (2 : MvPolynomial σ R) = 0 := by
      exact CharP.cast_eq_zero (MvPolynomial σ R) 2
    rw [htwo, zero_mul, zero_add]
  rw [hcast, one_mul]

/-- The coefficient `2N+1` is a unit scalar in characteristic two. -/
theorem odd_degree_cast_eq_one (N : Nat) :
    ((2 * N + 1 : Nat) : R) = 1 := by
  push_cast
  have htwo : (2 : R) = 0 := by
    exact CharP.cast_eq_zero R 2
  rw [htwo, zero_mul, zero_add]

/-- A square has zero ordinary partial derivative in characteristic two. -/
theorem pderiv_square_zero (i : σ) (G : MvPolynomial σ R) :
    MvPolynomial.pderiv i (G ^ 2) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  reduce_mod_char
  simp

/-- Adding a square does not change the ordinary Jacobian packet. -/
theorem pderiv_square_cleaning (i : σ) (H G : MvPolynomial σ R) :
    MvPolynomial.pderiv i (H + G ^ 2) = MvPolynomial.pderiv i H := by
  rw [map_add, pderiv_square_zero]
  simp

end EulerRadicial
end PCRLean
