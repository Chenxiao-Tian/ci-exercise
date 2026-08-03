import Mathlib
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import PCRLean.Experimental.IntrinsicCentreGaugeInvariance
import PCRLean.Experimental.SurjectiveFreeRegularCentre
import PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular

/-!
# Experimental regular centres from range restriction

Every linear map factors canonically as a surjection onto its range followed by
the range inclusion. Mathlib proves that `rangeRestrict` is surjective and has
exactly the same kernel as the original map. Therefore the intrinsic centre
ideal attached to an arbitrary linear packet is already the intrinsic centre
ideal of a surjection onto its image.

Consequently, whenever the image module is free, the quotient by the actual
kernel ideal is the symmetric algebra of that image. If the ambient module and
the image are finite free over a nontrivial regular base ring, the kernel ideal
is proper and finite type and its quotient is regular. Over a field, finite
dimensionality of the source makes all image-module hypotheses automatic.

This is a major reduction of U2: the remaining local geometric problem is not
to manufacture a surjective packet, but to prove that the image of the
Frobenius/Fitting packet is finite locally free on a finite principal-open
stratification. Localization compatibility, overlap descent, owner legality and
hereditary blowup transport remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace RangeRestrictedRegularCentre

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

open SurjectiveLinearMapSymmetricQuotient

/-- Canonical surjection of a linear packet onto its own image. -/
abbrev rangeProject (project : V →ₗ[R] W) :
    V →ₗ[R] LinearMap.range project :=
  project.rangeRestrict

/-- Range restriction is always surjective. -/
theorem rangeProject_surjective (project : V →ₗ[R] W) :
    Function.Surjective (rangeProject project) :=
  LinearMap.surjective_rangeRestrict project

/-- Range restriction does not alter the source kernel. -/
theorem ker_rangeProject (project : V →ₗ[R] W) :
    LinearMap.ker (rangeProject project) = LinearMap.ker project :=
  LinearMap.ker_rangeRestrict project

/-- Hence the intrinsic actual centre ideal is literally unchanged. -/
theorem kernelIdeal_rangeProject_eq (project : V →ₗ[R] W) :
    kernelIdeal (rangeProject project) = kernelIdeal project := by
  exact IntrinsicCentreGaugeInvariance.kernelIdeal_eq_of_ker_eq
    (rangeProject project) project (ker_rangeProject project)

/-- If the image module is free, every linear packet has an exact intrinsic
symmetric-algebra quotient by its image. -/
noncomputable def quotientEquiv
    (project : V →ₗ[R] W)
    [Module.Free R (LinearMap.range project)] :
    (SymmetricAlgebra R V ⧸ kernelIdeal project) ≃+*
      SymmetricAlgebra R (LinearMap.range project) :=
  (Ideal.quotEquivOfEq (kernelIdeal_rangeProject_eq project).symm).trans
    (SurjectiveLinearMapSymmetricQuotient.quotientEquiv
      (rangeProject project) (rangeProject_surjective project))

/-- Properness of the intrinsic centre follows from nontriviality of the image
symmetric algebra. -/
theorem kernelIdeal_ne_top
    (project : V →ₗ[R] W)
    [Module.Free R (LinearMap.range project)]
    [Nontrivial (SymmetricAlgebra R (LinearMap.range project))] :
    kernelIdeal project ≠ ⊤ := by
  rw [← kernelIdeal_rangeProject_eq project]
  exact SurjectiveLinearMapSymmetricQuotient.kernelIdeal_ne_top
    (rangeProject project) (rangeProject_surjective project)

/-- Regular actual-centre certificate expressed directly in terms of the
original possibly nonsurjective packet. -/
structure Certificate (project : V →ₗ[R] W) where
  ideal : Ideal (SymmetricAlgebra R V)
  ideal_eq : ideal = kernelIdeal project
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (SymmetricAlgebra R V ⧸ ideal) ≃+*
      SymmetricAlgebra R (LinearMap.range project)
  quotientRegular : IsRegularRing (SymmetricAlgebra R V ⧸ ideal)

/-- Assemble the certificate once the image symmetric algebra is regular and
the ambient symmetric algebra is Noetherian. -/
noncomputable def certificate
    (project : V →ₗ[R] W)
    [Module.Free R (LinearMap.range project)]
    [Nontrivial (SymmetricAlgebra R (LinearMap.range project))]
    [IsNoetherianRing (SymmetricAlgebra R V)]
    [IsRegularRing (SymmetricAlgebra R (LinearMap.range project))] :
    Certificate project where
  ideal := kernelIdeal project
  ideal_eq := rfl
  proper := kernelIdeal_ne_top project
  finiteType := IsNoetherian.noetherian _
  quotient := quotientEquiv project
  quotientRegular := IsRegularRing.of_ringEquiv
    (quotientEquiv project).symm

/-- Over a nontrivial regular base, finite freeness of the ambient module and
the image module makes every ring-theoretic hypothesis automatic. -/
noncomputable def finiteFreeCertificate
    [Nontrivial R] [IsRegularRing R]
    (project : V →ₗ[R] W)
    [Module.Free R V] [Module.Finite R V]
    [Module.Free R (LinearMap.range project)]
    [Module.Finite R (LinearMap.range project)] :
    Certificate project := by
  letI : IsNoetherianRing (SymmetricAlgebra R V) :=
    FiniteFreeSymmetricAlgebraRegular.isNoetherianRing
      (K := R) (M := V)
  letI : IsRegularRing
      (SymmetricAlgebra R (LinearMap.range project)) :=
    FiniteFreeSymmetricAlgebraRegular.isRegularRing
      (K := R) (M := LinearMap.range project)
  exact certificate project

/-- Over a field, every finite-dimensional linear packet automatically satisfies
all finite-free image hypotheses. No assumption on the codomain dimension or
on surjectivity is needed. -/
noncomputable def finiteDimensionalCertificate
    {K : Type*} [Field K]
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    [FiniteDimensional K E]
    (project : E →ₗ[K] F) :
    Certificate project := by
  exact finiteFreeCertificate project

end

end RangeRestrictedRegularCentre
end Experimental
end PCRLean
