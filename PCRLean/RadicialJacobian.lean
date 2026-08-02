import Mathlib
import PCRLean.EulerRadicial

namespace PCRLean
namespace RadicialJacobian

variable {R : Type*} {σ : Type*}
variable [CommRing R] [CharP R 2] [Fintype σ] [DecidableEq σ]

/-- The ordinary Jacobian ideal of a multivariate polynomial. -/
noncomputable def jacobianIdeal (H : MvPolynomial σ R) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun i : σ => MvPolynomial.pderiv i H)

/-- Every partial derivative is a generator of the Jacobian ideal. -/
theorem pderiv_mem_jacobian (H : MvPolynomial σ R) (i : σ) :
    MvPolynomial.pderiv i H ∈ jacobianIdeal H := by
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Multiplying a Jacobian generator by a coordinate remains in the Jacobian
ideal. -/
theorem X_mul_pderiv_mem (H : MvPolynomial σ R) (i : σ) :
    MvPolynomial.X i * MvPolynomial.pderiv i H ∈ jacobianIdeal H := by
  exact (jacobianIdeal H).mul_mem_left _ (pderiv_mem_jacobian H i)

/-- For an odd homogeneous polynomial in characteristic two, the equation
itself belongs to its Jacobian ideal. -/
theorem self_mem_jacobian_of_odd_homogeneous
    {H : MvPolynomial σ R} {N : Nat}
    (hH : H.IsHomogeneous (2 * N + 1)) : H ∈ jacobianIdeal H := by
  have hsum :
      (∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i H) ∈ jacobianIdeal H := by
    exact (jacobianIdeal H).sum_mem fun i _ => X_mul_pderiv_mem H i
  exact Eq.mp
    (congrArg (fun Q : MvPolynomial σ R => Q ∈ jacobianIdeal H)
      (EulerRadicial.odd_euler_identity hH))
    hsum

/-- Square cleaning leaves the full Jacobian ideal unchanged. -/
theorem jacobianIdeal_square_cleaning (H G : MvPolynomial σ R) :
    jacobianIdeal (H + G ^ 2) = jacobianIdeal H := by
  apply le_antisymm
  · rw [jacobianIdeal, jacobianIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    change MvPolynomial.pderiv i (H + G ^ 2) ∈
      Ideal.span (Set.range fun j : σ => MvPolynomial.pderiv j H)
    rw [EulerRadicial.pderiv_square_cleaning]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [jacobianIdeal, jacobianIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    change MvPolynomial.pderiv i H ∈
      Ideal.span (Set.range fun j : σ => MvPolynomial.pderiv j (H + G ^ 2))
    rw [← EulerRadicial.pderiv_square_cleaning i H G]
    exact Ideal.subset_span ⟨i, rfl⟩

/-- The principal ideal of an odd homogeneous equation is contained in its
Jacobian ideal. -/
theorem span_singleton_le_jacobian_of_odd_homogeneous
    {H : MvPolynomial σ R} {N : Nat}
    (hH : H.IsHomogeneous (2 * N + 1)) :
    Ideal.span {H} ≤ jacobianIdeal H := by
  rw [Ideal.span_le]
  simpa using self_mem_jacobian_of_odd_homogeneous hH

end RadicialJacobian
end PCRLean
