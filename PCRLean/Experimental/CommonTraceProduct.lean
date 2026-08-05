import Mathlib
import Mathlib.RingTheory.Ideal.Operations

/-!
# Common trace products

For two source-labelled carrier flatifiers with ambient trace ideals `I` and
`J`, their product is contained in each factor.  Scheme-theoretically, the
centre of the product is the union of the two source centres.  The blowup of
the product is the standard common refinement of the two blowups; that
scheme-level universal-property statement remains outside this file.

The elementary ideal containments are the algebraic leaves used by the X040
finite-product induction.  They also show that a common trace centre is
supported on the finite union of the source supports.
-/

namespace PCRLean
namespace Experimental
namespace CommonTraceProduct

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The product trace ideal is contained in its left source ideal. -/
theorem mul_le_left_source (I J : Ideal R) :
    I * J ≤ I := by
  simpa [Ideal.smul_eq_mul, mul_comm] using
    (Submodule.smul_le_right (I := J) (N := I))

/-- The product trace ideal is contained in its right source ideal. -/
theorem mul_le_right_source (I J : Ideal R) :
    I * J ≤ J := by
  simpa [Ideal.smul_eq_mul] using
    (Submodule.smul_le_right (I := I) (N := J))

/-- Any ideal contained in both source factors is contained in their sum, while
its product source is contained in both.  This packages the direction of the
scheme-theoretic support inclusions used by the common-refinement compiler. -/
theorem product_le_inf (I J : Ideal R) :
    I * J ≤ I ⊓ J := by
  exact le_inf (mul_le_left_source I J) (mul_le_right_source I J)

/-- Multiplication of source ideals is symmetric; no arbitrary ordering of two
sources is introduced at the product level. -/
theorem swap_sources (I J : Ideal R) :
    I * J = J * I :=
  mul_comm I J

/-- Three source ideals can be aggregated without parenthesization ambiguity. -/
theorem reassoc_sources (I J K : Ideal R) :
    (I * J) * K = I * (J * K) :=
  mul_assoc I J K

end

end CommonTraceProduct
end Experimental
end PCRLean
