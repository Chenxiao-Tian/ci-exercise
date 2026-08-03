import Mathlib
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.SplitMatrixMarkedHybridCompiler
import PCRLean.Experimental.PolynomialGraphBoundaryIntersection
import PCRLean.Experimental.PolynomialGraphFrobeniusCentreCertificate

/-!
# Proper regular hybrid centres from coefficient closures

For the marked split-packet compiler, let `K` be the selected coefficient
closure and let

`C = (Z_i-h_i) + K R[Z]`.

This is exactly the graph--coefficient intersection ideal of
`PolynomialGraphBoundaryIntersection`, hence

`R[Z] / C ≃ R / K`.

Consequently:

* `K ≠ R` implies `C ≠ R`;
* a nonempty graph direction makes `C ≠ 0`;
* Noetherianity gives finite type; and
* regularity of `R/K` gives regularity of the closed centre.

Thus the regularity and properness gates for the graph-plus-order-ideal hybrid
reduce completely to the corresponding gates for the coefficient marked
closure.
-/

namespace PCRLean
namespace Experimental
namespace SplitMatrixMarkedHybridRegularCentre

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] [IsDomain R]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {Component : Type x} [Fintype Component] [DecidableEq Component]
variable {Owner : Type y} [Fintype Owner]

open SplitMatrixOrderIdealHybrid
open OrderIdealMarkedClosureCompiler
open SplitMatrixMarkedHybridCompiler
open PolynomialGraphBoundaryIntersection

variable {M : Matrix κ ι R}
variable (S : SplitMatrixOrderIdealHybrid.SplitPacket M)
variable (b : SplitMatrixOrderIdealHybrid.Target (R := R) (κ := κ))
variable (component : Component → Ideal R)
variable (Q : Requirements (R := R) (Owner := Owner))
variable
  (hfull : Acceptable (S.defectIdeal b) component Q Finset.univ)

abbrev K : Ideal R :=
  coefficientClosure S b component Q hfull

abbrev C : Ideal (MvPolynomial ι R) :=
  centreIdeal S b component Q hfull

/-- The selected hybrid centre is exactly the standard graph--coefficient
intersection ideal. -/
theorem centreIdeal_eq_combinedIdeal :
    C S b component Q hfull =
      combinedIdeal (S.graph b) (K S b component Q hfull) := by
  rfl

/-- Exact quotient of the selected hybrid centre. -/
noncomputable def quotientEquiv :
    (MvPolynomial ι R ⧸ C S b component Q hfull) ≃+*
      (R ⧸ K S b component Q hfull) := by
  rw [centreIdeal_eq_combinedIdeal]
  exact PolynomialGraphBoundaryIntersection.quotientEquiv
    (S.graph b) (K S b component Q hfull)

/-- A proper coefficient closure gives a proper polynomial hybrid centre. -/
theorem centreIdeal_ne_top
    (hK : K S b component Q hfull ≠ ⊤) :
    C S b component Q hfull ≠ ⊤ := by
  intro htop
  have hmem : (1 : MvPolynomial ι R) ∈
      C S b component Q hfull := by
    rw [htop]
    trivial
  rw [centreIdeal_eq_combinedIdeal,
    combinedIdeal_eq_comap] at hmem
  have hOne : (1 : R) ∈ K S b component Q hfull := by
    simpa [PolynomialGraphCentreQuotient.graphEval] using hmem
  exact hK (Ideal.eq_top_iff_one.mpr hOne)

/-- The nonempty graph component prevents the hybrid centre from being the
whole ambient space as a closed subset. -/
theorem centreIdeal_ne_bot :
    C S b component Q hfull ≠ ⊥ := by
  intro hbot
  have hle :
      PolynomialGraphCentreHeredity.graphIdeal (S.graph b) ≤
        C S b component Q hfull :=
    le_sup_left
  have hgraph :
      PolynomialGraphCentreHeredity.graphIdeal (S.graph b) = ⊥ := by
    apply le_antisymm
    · simpa [hbot] using hle
    · exact bot_le
  exact PolynomialGraphFrobeniusCentreCertificate.graphIdeal_ne_bot
    (S.graph b) hgraph

/-- Noetherian ambient polynomial rings make the selected hybrid centre finite
type. -/
theorem centreIdeal_fg
    [IsNoetherianRing (MvPolynomial ι R)] :
    (C S b component Q hfull).FG :=
  IsNoetherian.noetherian _

/-- Regularity of the coefficient closure quotient transfers exactly to the
hybrid centre. -/
theorem quotient_isRegularRing
    [IsRegularRing (R ⧸ K S b component Q hfull)] :
    IsRegularRing (MvPolynomial ι R ⧸ C S b component Q hfull) := by
  exact IsRegularRing.of_ringEquiv
    (quotientEquiv S b component Q hfull).symm

/-- Complete actual proper finite-type regular hybrid-centre certificate. -/
structure Certificate where
  ideal : Ideal (MvPolynomial ι R)
  ideal_eq : ideal = C S b component Q hfull
  proper : ideal ≠ ⊤
  nonwhole : ideal ≠ ⊥
  finiteType : ideal.FG
  quotient :
    (MvPolynomial ι R ⧸ ideal) ≃+*
      (R ⧸ K S b component Q hfull)
  quotientRegular : IsRegularRing (MvPolynomial ι R ⧸ ideal)
  packetContainment :
    MaximalMinorEquationIdeal.equationIdeal M b ≤ ideal
  ownerContainment : ∀ o : Owner,
    Ideal.map MvPolynomial.C (Q.ownerIdeal o) ≤
      ideal ^ (Q.mark o)

/-- Assemble the regular hybrid-centre certificate once the coefficient closure
passes its own properness and regularity gates. -/
noncomputable def certificate
    [IsNoetherianRing (MvPolynomial ι R)]
    [IsRegularRing (R ⧸ K S b component Q hfull)]
    (hK : K S b component Q hfull ≠ ⊤) :
    Certificate S b component Q hfull where
  ideal := C S b component Q hfull
  ideal_eq := rfl
  proper := centreIdeal_ne_top S b component Q hfull hK
  nonwhole := centreIdeal_ne_bot S b component Q hfull
  finiteType := centreIdeal_fg S b component Q hfull
  quotient := quotientEquiv S b component Q hfull
  quotientRegular := quotient_isRegularRing S b component Q hfull
  packetContainment :=
    SplitMatrixMarkedHybridCompiler.equationIdeal_le_centreIdeal
      S b component Q hfull
  ownerContainment := fun o =>
    SplitMatrixMarkedHybridCompiler.extended_ownerIdeal_le_centreIdeal_pow
      S b component Q hfull o

end

end SplitMatrixMarkedHybridRegularCentre
end Experimental
end PCRLean
