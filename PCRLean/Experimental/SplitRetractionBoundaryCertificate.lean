import Mathlib
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.SplitRetractionBoundaryQuotient

/-!
# Regular boundary-stratum certificates for split retractions

For a split retraction `A → B` and an ideal `J ⊂ B`, the combined ideal

`ker(project) ⊔ map(section, J)`

has quotient exactly `B/J`.  This file packages the consequences needed from a
local graph model:

* exact quotient;
* properness whenever `J` is proper;
* finite generation over a Noetherian ambient ring; and
* regularity whenever the boundary stratum `B/J` is regular.

This is a certificate for regular scheme-theoretic intersections.  It does not
by itself prove simple normal crossings: conormal direct-sum and codimension
additivity are retained as separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace SplitRetractionBoundaryCertificate

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

open SplitRetractionBoundaryQuotient

variable (S : Retraction (A := A) (B := B))

/-- A proper boundary ideal lifts to a proper combined centre-boundary ideal. -/
theorem liftedBoundaryIdeal_ne_top
    (J : Ideal B) (hJ : J ≠ ⊤) :
    S.liftedBoundaryIdeal J ≠ ⊤ := by
  intro htop
  have htopLift : S.liftedBoundaryIdeal (⊤ : Ideal B) = ⊤ := by
    apply top_unique
    intro a ha
    have hsection : S.section (S.project a) ∈
        (⊤ : Ideal B).map S.section :=
      Ideal.mem_map_of_mem S.section trivial
    have hkernel : a - S.section (S.project a) ∈ RingHom.ker S.project := by
      apply RingHom.mem_ker.mpr
      simp
    have hleft : a - S.section (S.project a) ∈
        S.liftedBoundaryIdeal (⊤ : Ideal B) :=
      le_sup_left hkernel
    have hright : S.section (S.project a) ∈
        S.liftedBoundaryIdeal (⊤ : Ideal B) :=
      le_sup_right hsection
    simpa using
      (S.liftedBoundaryIdeal (⊤ : Ideal B)).add_mem hleft hright
  apply hJ
  apply S.liftedBoundaryIdeal_injective
  exact htop.trans htopLift.symm

/-- Regularity of the boundary stratum transfers to the combined quotient. -/
theorem quotient_isRegularRing
    (J : Ideal B) [IsRegularRing (B ⧸ J)] :
    IsRegularRing (A ⧸ S.liftedBoundaryIdeal J) := by
  exact IsRegularRing.of_ringEquiv (S.quotientEquiv J).symm

/-- Full affine boundary-stratum certificate. -/
structure Certificate (J : Ideal B) where
  combinedIdeal : Ideal A
  combinedIdeal_eq : combinedIdeal = S.liftedBoundaryIdeal J
  proper : combinedIdeal ≠ ⊤
  finiteType : combinedIdeal.FG
  quotient : (A ⧸ combinedIdeal) ≃+* (B ⧸ J)
  quotientRegular : IsRegularRing (A ⧸ combinedIdeal)

/-- Assemble the certificate over a Noetherian ambient ring. -/
noncomputable def certificate
    [IsNoetherianRing A]
    (J : Ideal B) (hJ : J ≠ ⊤)
    [IsRegularRing (B ⧸ J)] :
    Certificate S J where
  combinedIdeal := S.liftedBoundaryIdeal J
  combinedIdeal_eq := rfl
  proper := S.liftedBoundaryIdeal_ne_top J hJ
  finiteType := IsNoetherian.noetherian _
  quotient := S.quotientEquiv J
  quotientRegular := S.quotient_isRegularRing J

end

end SplitRetractionBoundaryCertificate
end Experimental
end PCRLean
