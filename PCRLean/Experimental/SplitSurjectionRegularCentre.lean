import Mathlib
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.SplitSurjectionActualCentre

/-!
# Experimental regular centre from a split surjection

The intrinsic split-surjection ideal has an exact quotient by the target
symmetric algebra.  Whenever that target is a regular ring, regularity transfers
back across the quotient equivalence.  Combining this with properness and
Noetherian finite generation yields an affine certificate whose closed centre
ring is regular.

This proves regularity of the centre as an affine scheme in the stated chamber.
It does not prove that an arbitrary Frobenius/Fitting core supplies the split
surjection, nor does it prove boundary transversality, hereditary transforms,
or global gluing.
-/

namespace PCRLean
namespace Experimental
namespace SplitSurjectionRegularCentre

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} {Kmod : Type w}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup Kmod] [Module R Kmod]

open SplitSurjectionSymmetricQuotient
open SplitSurjectionActualCentre

variable (S : SplitSurjection (R := R) (V := V) (Kmod := Kmod))

/-- Regularity of the target symmetric algebra transfers to the actual centre
quotient. -/
theorem quotient_isRegularRing
    [IsRegularRing (SymmetricAlgebra R Kmod)] :
    IsRegularRing (SymmetricAlgebra R V ⧸ S.kernelIdeal) := by
  exact IsRegularRing.of_ringEquiv S.quotientEquiv.symm

/-- Actual finite-type centre certificate enhanced by regularity of its affine
coordinate ring. -/
structure Certificate where
  ideal : Ideal (SymmetricAlgebra R V)
  ideal_eq : ideal = S.kernelIdeal
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (SymmetricAlgebra R V ⧸ ideal) ≃+* SymmetricAlgebra R Kmod
  quotientRegular : IsRegularRing (SymmetricAlgebra R V ⧸ ideal)

/-- Assemble the regular affine-centre certificate. -/
noncomputable def certificate
    [Nontrivial (SymmetricAlgebra R Kmod)]
    [IsNoetherianRing (SymmetricAlgebra R V)]
    [IsRegularRing (SymmetricAlgebra R Kmod)] :
    Certificate S where
  ideal := S.kernelIdeal
  ideal_eq := rfl
  proper := SplitSurjectionActualCentre.kernelIdeal_ne_top S
  finiteType := SplitSurjectionActualCentre.kernelIdeal_fg S
  quotient := S.quotientEquiv
  quotientRegular := quotient_isRegularRing S

end

end SplitSurjectionRegularCentre
end Experimental
end PCRLean
