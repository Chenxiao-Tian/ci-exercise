import Mathlib
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Regularity of finite-dimensional symmetric algebras over a field

A finite-dimensional vector space admits a basis indexed by a finite type. Its
symmetric algebra is algebra-equivalent to a multivariate polynomial ring in
finitely many variables. Polynomial regularity and invariance under ring
equivalence imply that the symmetric algebra is regular.

This removes the abstract regular-target assumption from the intrinsic
split-surjection centre construction in the finite-dimensional field chamber.
-/

namespace PCRLean
namespace Experimental
namespace FiniteDimensionalSymmetricRegularBridge

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]

/-- A finite-dimensional symmetric algebra over a field is a regular ring. -/
theorem isRegularRing [FiniteDimensional K M] :
    IsRegularRing (SymmetricAlgebra K M) := by
  let b := FiniteDimensional.finBasis K M
  exact IsRegularRing.of_ringEquiv
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv

end

end FiniteDimensionalSymmetricRegularBridge
end Experimental
end PCRLean
