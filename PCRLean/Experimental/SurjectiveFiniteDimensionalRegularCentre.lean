import Mathlib
import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality
import PCRLean.Experimental.FiniteDimensionalIntrinsicRegularCentre

/-!
# Experimental intrinsic regular centre from a finite-dimensional surjection

Over a field, every surjective linear map admits a linear right inverse.  The
right inverse is used only to prove the quotient theorem; the actual centre
ideal is defined intrinsically from the kernel of the original map.  Therefore
a surjection between finite-dimensional vector spaces determines an actual
proper finite-type ideal with regular symmetric-algebra quotient, without a
chosen splitting in the theorem interface.

This removes one choice from the U2 chamber.  It does not construct the
surjective conormal map from arbitrary Frobenius/Fitting data and does not prove
marked permissibility, boundary compatibility, hereditary blowup transport, or
global descent.
-/

namespace PCRLean
namespace Experimental
namespace SurjectiveFiniteDimensionalRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

open SplitSurjectionSymmetricQuotient
open IntrinsicKernelIdealFunctoriality

/-- A chosen linear right inverse of a surjective map. -/
noncomputable def rightInvOfSurjective
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) : W →ₗ[K] V :=
  Classical.choose
    (project.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hproject))

/-- The chosen map is a genuine right inverse. -/
theorem rightInvOfSurjective_spec
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    project.comp (rightInvOfSurjective project hproject) = LinearMap.id :=
  Classical.choose_spec
    (project.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hproject))

/-- Split-surjection package extracted from surjectivity. -/
noncomputable def splitSurjectionOfSurjective
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    SplitSurjection (R := K) (V := V) (Kmod := W) where
  project := project
  liftBack := rightInvOfSurjective project hproject
  rightInverse := rightInvOfSurjective_spec project hproject

/-- Intrinsic actual ideal attached to the original surjection. -/
def centreIdeal (project : V →ₗ[K] W) :
    Ideal (SymmetricAlgebra K V) :=
  kernelIdealOf project

/-- The split package uses exactly the intrinsic ideal of the original map. -/
theorem split_kernelIdeal_eq_centreIdeal
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    (splitSurjectionOfSurjective project hproject).kernelIdeal =
      centreIdeal project := by
  rfl

/-- Exact quotient theorem, independent in its statement from the chosen right
inverse. -/
noncomputable def quotientEquiv
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    (SymmetricAlgebra K V ⧸ centreIdeal project) ≃+*
      SymmetricAlgebra K W := by
  simpa [split_kernelIdeal_eq_centreIdeal] using
    (splitSurjectionOfSurjective project hproject).quotientEquiv

section FiniteDimensional

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Complete actual, proper, finite-type, regular centre certificate associated
to a finite-dimensional surjection. -/
noncomputable def regularCentreCertificate
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    SplitSurjectionRegularCentre.Certificate
      (splitSurjectionOfSurjective project hproject) :=
  FiniteDimensionalIntrinsicRegularCentre.certificate
    (splitSurjectionOfSurjective project hproject)

/-- Properness of the intrinsic surjection centre. -/
theorem centreIdeal_ne_top
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    centreIdeal project ≠ ⊤ := by
  rw [← split_kernelIdeal_eq_centreIdeal project hproject]
  exact FiniteDimensionalIntrinsicRegularCentre.kernelIdeal_ne_top
    (splitSurjectionOfSurjective project hproject)

/-- Finite generation of the intrinsic surjection centre. -/
theorem centreIdeal_fg
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    (centreIdeal project).FG := by
  rw [← split_kernelIdeal_eq_centreIdeal project hproject]
  exact FiniteDimensionalIntrinsicRegularCentre.kernelIdeal_fg
    (splitSurjectionOfSurjective project hproject)

/-- Regularity of the intrinsic quotient. -/
theorem quotient_isRegularRing
    (project : V →ₗ[K] W)
    (hproject : Function.Surjective project) :
    IsRegularRing (SymmetricAlgebra K V ⧸ centreIdeal project) := by
  rw [← split_kernelIdeal_eq_centreIdeal project hproject]
  exact FiniteDimensionalIntrinsicRegularCentre.quotient_isRegularRing
    (splitSurjectionOfSurjective project hproject)

end FiniteDimensional

end

end SurjectiveFiniteDimensionalRegularCentre
end Experimental
end PCRLean
