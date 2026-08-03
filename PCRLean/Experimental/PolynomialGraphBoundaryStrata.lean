import Mathlib
import PCRLean.Experimental.PolynomialGraphBoundaryIntersection

/-!
# Finite regular boundary strata for polynomial graph centres

A simple-normal-crossings boundary is controlled by all finite intersections of
its components.  At the affine ring level, let `B_j ⊂ R` be a finite family of
boundary-component ideals and let

`J_S = ∑_{j∈S} B_j`

be the ideal of one boundary stratum.  If every quotient `R/J_S` is regular,
then the polynomial graph centre meets every stratum regularly, with exact
quotient

`R[Z_i] / (I_h + (J_S)_P) ≃ R / J_S`.

This theorem packages all finite strata at once.  It captures the regular
intersection part of SNC compatibility in the graph chamber.  Codimension
additivity, divisor multiplicities and the global combinatorics of the total
boundary remain separate scheme-level obligations.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBoundaryStrata

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]
variable {β : Type w} [Fintype β] [DecidableEq β]

open PolynomialGraphBoundaryIntersection

abbrev P := MvPolynomial ι R

/-- Ideal of a finite boundary stratum. -/
def stratumIdeal
    (boundary : β → Ideal R) (s : Finset β) : Ideal R :=
  ∑ j in s, boundary j

/-- A finite boundary family whose every stratum has regular coordinate ring. -/
structure RegularBoundaryFamily (boundary : β → Ideal R) : Prop where
  strataRegular : ∀ s : Finset β,
    IsRegularRing (R ⧸ stratumIdeal boundary s)

/-- Actual graph--boundary intersection ideal for one finite stratum. -/
def graphStratumIdeal
    (h : ι → R) (boundary : β → Ideal R) (s : Finset β) :
    Ideal (P (R := R) (ι := ι)) :=
  combinedIdeal h (stratumIdeal boundary s)

/-- Every graph--boundary stratum has the expected exact quotient. -/
noncomputable def graphStratumQuotientEquiv
    (h : ι → R) (boundary : β → Ideal R) (s : Finset β) :
    (P (R := R) (ι := ι) ⧸ graphStratumIdeal h boundary s) ≃+*
      (R ⧸ stratumIdeal boundary s) :=
  PolynomialGraphBoundaryIntersection.quotientEquiv
    h (stratumIdeal boundary s)

/-- A regular boundary family remains regular after restriction to the graph
centre, stratum by stratum. -/
theorem graphStratum_isRegularRing
    (h : ι → R) (boundary : β → Ideal R)
    (hboundary : RegularBoundaryFamily boundary)
    (s : Finset β) :
    IsRegularRing
      (P (R := R) (ι := ι) ⧸ graphStratumIdeal h boundary s) := by
  letI : IsRegularRing (R ⧸ stratumIdeal boundary s) :=
    hboundary.strataRegular s
  exact PolynomialGraphBoundaryIntersection.quotient_isRegularRing
    h (stratumIdeal boundary s)

/-- Finite all-strata boundary certificate. -/
structure Certificate
    (h : ι → R) (boundary : β → Ideal R) where
  quotient : ∀ s : Finset β,
    (P (R := R) (ι := ι) ⧸ graphStratumIdeal h boundary s) ≃+*
      (R ⧸ stratumIdeal boundary s)
  regular : ∀ s : Finset β,
    IsRegularRing
      (P (R := R) (ι := ι) ⧸ graphStratumIdeal h boundary s)

/-- Assemble the all-strata certificate. -/
noncomputable def certificate
    (h : ι → R) (boundary : β → Ideal R)
    (hboundary : RegularBoundaryFamily boundary) :
    Certificate h boundary where
  quotient := graphStratumQuotientEquiv h boundary
  regular := graphStratum_isRegularRing h boundary hboundary

end

end PolynomialGraphBoundaryStrata
end Experimental
end PCRLean
