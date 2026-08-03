import Mathlib
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient

/-!
# Experimental regular centre from a surjection onto a free module

The geometric input is now only a surjective linear map onto a free target.
A right inverse is constructed internally from a free basis, while the actual
centre ideal is defined intrinsically from the kernel of the original map.
Under Noetherianity of the ambient symmetric algebra and regularity of the
target symmetric algebra, this gives a proper finite-type actual ideal with an
exact regular quotient.

This removes a chosen splitting from the theorem statement. It still does not
construct the surjective locally free quotient from an arbitrary
Frobenius/Fitting core, prove overlap descent, or establish hereditary blowup
transport.
-/

namespace PCRLean
namespace Experimental
namespace SurjectiveFreeRegularCentre

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {Kmod : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup Kmod] [Module R Kmod]
variable [Module.Free R Kmod]

open SurjectiveLinearMapSymmetricQuotient

/-- A regular actual-centre certificate whose ideal depends only on the
surjective map. -/
structure Certificate
    (project : V →ₗ[R] Kmod) where
  ideal : Ideal (SymmetricAlgebra R V)
  ideal_eq : ideal = kernelIdeal project
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (SymmetricAlgebra R V ⧸ ideal) ≃+* SymmetricAlgebra R Kmod
  quotientRegular : IsRegularRing (SymmetricAlgebra R V ⧸ ideal)

/-- Regularity transfers across the intrinsic quotient equivalence. -/
theorem quotient_isRegularRing
    [IsRegularRing (SymmetricAlgebra R Kmod)]
    (project : V →ₗ[R] Kmod)
    (hproject : Function.Surjective project) :
    IsRegularRing
      (SymmetricAlgebra R V ⧸ kernelIdeal project) := by
  exact IsRegularRing.of_ringEquiv
    (quotientEquiv project hproject).symm

/-- Assemble the intrinsic regular-centre certificate from surjectivity onto a
free module. -/
noncomputable def certificate
    [Nontrivial (SymmetricAlgebra R Kmod)]
    [IsNoetherianRing (SymmetricAlgebra R V)]
    [IsRegularRing (SymmetricAlgebra R Kmod)]
    (project : V →ₗ[R] Kmod)
    (hproject : Function.Surjective project) :
    Certificate project where
  ideal := kernelIdeal project
  ideal_eq := rfl
  proper := kernelIdeal_ne_top project hproject
  finiteType := IsNoetherian.noetherian _
  quotient := quotientEquiv project hproject
  quotientRegular := quotient_isRegularRing project hproject

end

end SurjectiveFreeRegularCentre
end Experimental
end PCRLean
