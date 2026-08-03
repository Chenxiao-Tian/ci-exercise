import Mathlib
import PCRLean.Experimental.PolynomialGraphCentreQuotient
import PCRLean.Experimental.SplitRetractionBoundaryCertificate

/-!
# Boundary strata of polynomial graph centres

For a polynomial graph centre in `R[Z_i]`, let `J ⊂ R` be a boundary-stratum
ideal in the coefficient ring.  The scheme-theoretic intersection is defined by

`I_h ⊔ map(C, J)`.

Graph evaluation is a split retraction with section `C`.  The general split
retraction theorem therefore gives the exact quotient

`R[Z_i] / (I_h + C(J)) ≃ R / J`.

Hence every regular boundary stratum in the coefficient ring produces a
regular scheme-theoretic intersection with the graph centre.  This is the
regular-strata part of SNC compatibility; conormal direct-sum and codimension
additivity remain explicit separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBoundaryStratum

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]

open PolynomialGraphCentreHeredity
open PolynomialGraphCentreQuotient
open SplitRetractionBoundaryQuotient
open SplitRetractionBoundaryCertificate

abbrev P := MvPolynomial ι R

/-- Graph evaluation together with the coefficient inclusion. -/
noncomputable def graphRetraction (h : ι → R) :
    Retraction (A := P (R := R) (ι := ι)) (B := R) where
  project := graphEval h
  section := MvPolynomial.C
  project_section := by
    ext r
    simp [graphEval]

/-- Actual ideal of the graph-centre intersection with a coefficient-ring
boundary stratum. -/
def combinedIdeal (h : ι → R) (J : Ideal R) :
    Ideal (P (R := R) (ι := ι)) :=
  graphIdeal h ⊔ J.map MvPolynomial.C

/-- The split-retraction lifted ideal is exactly the graph-boundary combined
ideal. -/
theorem liftedBoundaryIdeal_eq_combinedIdeal
    (h : ι → R) (J : Ideal R) :
    (graphRetraction h).liftedBoundaryIdeal J = combinedIdeal h J := by
  rw [Retraction.liftedBoundaryIdeal, combinedIdeal]
  rw [ker_graphEval_eq_graphIdeal]

/-- Exact quotient of every graph-boundary stratum. -/
noncomputable def quotientEquiv
    (h : ι → R) (J : Ideal R) :
    (P (R := R) (ι := ι) ⧸ combinedIdeal h J) ≃+* (R ⧸ J) := by
  rw [← liftedBoundaryIdeal_eq_combinedIdeal h J]
  exact (graphRetraction h).quotientEquiv J

/-- A proper boundary stratum gives a proper combined ideal. -/
theorem combinedIdeal_ne_top
    (h : ι → R) (J : Ideal R) (hJ : J ≠ ⊤) :
    combinedIdeal h J ≠ ⊤ := by
  rw [← liftedBoundaryIdeal_eq_combinedIdeal h J]
  exact (graphRetraction h).liftedBoundaryIdeal_ne_top J hJ

/-- Regularity of the coefficient boundary stratum transfers to the
scheme-theoretic graph intersection. -/
theorem quotient_isRegularRing
    (h : ι → R) (J : Ideal R)
    [IsRegularRing (R ⧸ J)] :
    IsRegularRing (P (R := R) (ι := ι) ⧸ combinedIdeal h J) := by
  exact IsRegularRing.of_ringEquiv (quotientEquiv h J).symm

/-- Full regular boundary-stratum certificate. -/
structure Certificate (h : ι → R) (J : Ideal R) where
  intersectionIdeal : Ideal (P (R := R) (ι := ι))
  intersectionIdeal_eq : intersectionIdeal = combinedIdeal h J
  proper : intersectionIdeal ≠ ⊤
  finiteType : intersectionIdeal.FG
  quotient :
    (P (R := R) (ι := ι) ⧸ intersectionIdeal) ≃+* (R ⧸ J)
  quotientRegular :
    IsRegularRing (P (R := R) (ι := ι) ⧸ intersectionIdeal)

/-- Assemble the graph-boundary regular-stratum certificate. -/
noncomputable def certificate
    [IsNoetherianRing R] [Finite ι]
    (h : ι → R) (J : Ideal R) (hJ : J ≠ ⊤)
    [IsRegularRing (R ⧸ J)] :
    Certificate h J where
  intersectionIdeal := combinedIdeal h J
  intersectionIdeal_eq := rfl
  proper := combinedIdeal_ne_top h J hJ
  finiteType := IsNoetherian.noetherian _
  quotient := quotientEquiv h J
  quotientRegular := quotient_isRegularRing h J

end

end PolynomialGraphBoundaryStratum
end Experimental
end PCRLean
