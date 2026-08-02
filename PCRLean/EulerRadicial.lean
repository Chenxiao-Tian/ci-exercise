import Mathlib.RingTheory.MvPolynomial.EulerIdentity

namespace PCRLean
namespace EulerRadicial

variable {R : Type*} {σ : Type*}
variable [CommRing R] [CharP R 2] [Fintype σ]

private theorem two_eq_zero_poly : (2 : MvPolynomial σ R) = 0 := by
  change MvPolynomial.C (2 : R) = 0
  rw [CharP.cast_eq_zero R 2, map_zero]

/-- In characteristic two, Euler's homogeneous identity for an odd degree
`2N+1` has coefficient one. This is the algebraic core behind
`H = Σ xᵢ ∂ᵢH` in the nonprincipal radicial chambers. -/
theorem odd_euler_identity {H : MvPolynomial σ R} {N : Nat}
    (hH : H.IsHomogeneous (2 * N + 1)) :
    ∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i H = H := by
  rw [hH.sum_X_mul_pderiv]
  rw [nsmul_eq_mul]
  have hcast : ((2 * N + 1 : Nat) : MvPolynomial σ R) = 1 := by
    push_cast
    rw [two_eq_zero_poly, zero_mul, zero_add]
  rw [hcast, one_mul]

/-- The coefficient `2N+1` is one in characteristic two. -/
theorem odd_degree_cast_eq_one (N : Nat) :
    ((2 * N + 1 : Nat) : R) = 1 := by
  push_cast
  rw [CharP.cast_eq_zero R 2, zero_mul, zero_add]

/-- A square has zero ordinary partial derivative in characteristic two. -/
theorem pderiv_square_zero (i : σ) (G : MvPolynomial σ R) :
    MvPolynomial.pderiv i (G ^ 2) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  have htwo : (2 : MvPolynomial σ R) = 0 := two_eq_zero_poly
  rw [htwo, zero_mul]

/-- Adding a square does not change the ordinary Jacobian packet. -/
theorem pderiv_square_cleaning (i : σ) (H G : MvPolynomial σ R) :
    MvPolynomial.pderiv i (H + G ^ 2) = MvPolynomial.pderiv i H := by
  rw [map_add, pderiv_square_zero, add_zero]

end EulerRadicial
end PCRLean
