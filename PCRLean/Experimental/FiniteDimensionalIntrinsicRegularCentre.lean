import Mathlib
import PCRLean.Experimental.FiniteDimensionalSymmetricRegularBridge
import PCRLean.Experimental.SplitSurjectionRegularCentre

/-!
# Finite-dimensional intrinsic regular centres over a field

For a split surjection between finite-dimensional vector spaces over a field,
the intrinsic degree-one kernel ideal is an actual proper finitely generated
ideal and its quotient is a regular symmetric algebra. No coordinate basis or
chosen complement occurs in the definition of the ideal.

This closes the algebraic U2 chamber after a finite-dimensional split conormal
surjection has been geometrically constructed. It does not construct that
surjection from an arbitrary singularity and does not establish hereditary
blowup transport or global gluing.
-/

namespace PCRLean
namespace Experimental
namespace FiniteDimensionalIntrinsicRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} {Kmod : Type w}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup Kmod] [Module K Kmod]
variable [FiniteDimensional K V] [FiniteDimensional K Kmod]

open SplitSurjectionSymmetricQuotient

variable (S : SplitSurjection (R := K) (V := V) (Kmod := Kmod))

/-- Finite-dimensional symmetric algebras over a field are Noetherian. -/
theorem source_isNoetherianRing :
    IsNoetherianRing (SymmetricAlgebra K V) := by
  infer_instance

/-- The quotient by the intrinsic kernel ideal is regular without an external
regularity assumption. -/
theorem quotient_isRegularRing :
    IsRegularRing (SymmetricAlgebra K V ⧸ S.kernelIdeal) := by
  letI : IsRegularRing (SymmetricAlgebra K Kmod) :=
    FiniteDimensionalSymmetricRegularBridge.isRegularRing
  exact SplitSurjectionRegularCentre.quotient_isRegularRing S

/-- Complete actual, proper, finite-type, regular affine-centre certificate in
the finite-dimensional split chamber. -/
noncomputable def certificate :
    SplitSurjectionRegularCentre.Certificate S := by
  letI : IsRegularRing (SymmetricAlgebra K Kmod) :=
    FiniteDimensionalSymmetricRegularBridge.isRegularRing
  exact SplitSurjectionRegularCentre.certificate S

/-- The intrinsic centre ideal is proper. -/
theorem kernelIdeal_ne_top : S.kernelIdeal ≠ ⊤ :=
  SplitSurjectionActualCentre.kernelIdeal_ne_top S

/-- The intrinsic centre ideal is finitely generated. -/
theorem kernelIdeal_fg : S.kernelIdeal.FG :=
  SplitSurjectionActualCentre.kernelIdeal_fg S

end

end FiniteDimensionalIntrinsicRegularCentre
end Experimental
end PCRLean
