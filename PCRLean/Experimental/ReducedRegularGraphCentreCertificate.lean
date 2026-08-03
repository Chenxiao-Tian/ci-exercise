import Mathlib
import PCRLean.Experimental.ReducedGraphCentreQuotient
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity
import PCRLean.Experimental.PolynomialGraphCentreCotangentBasis

/-!
# Reduced regular graph-centre certificate

A polynomial graph centre over a reduced regular coefficient ring simultaneously
has all local algebraic properties required by the centre-synthesis layer:

* an actual finitely generated proper ideal;
* an exact quotient equal to the coefficient ring;
* a reduced and regular centre coordinate ring;
* a finite free conormal module; and
* exact prime-power marked heredity.

This file packages those results into one typed certificate.  It is an affine
local theorem.  A general resolution proof must still construct and glue such
models around arbitrary regular centres and verify owner, boundary, transform,
and history conditions.
-/

namespace PCRLean
namespace Experimental
namespace ReducedRegularGraphCentreCertificate

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [Nontrivial R]
variable [IsReduced R] [IsRegularRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable (p : Nat) [Fact p.Prime] [CharP R p]

open ReducedPolynomialGraphCentreHeredity

abbrev P := MvPolynomial ι R

/-- Complete local algebraic certificate for the graph `Z_i = h_i`. -/
structure Certificate (h : ι → R) where
  proper : graphIdeal h ≠ ⊤
  finiteType : (graphIdeal h).FG
  quotient : (P (R := R) (ι := ι) ⧸ graphIdeal h) ≃+* R
  quotientReduced : IsReduced (P (R := R) (ι := ι) ⧸ graphIdeal h)
  quotientRegular : IsRegularRing (P (R := R) (ι := ι) ⧸ graphIdeal h)
  conormal : (graphIdeal h).Cotangent ≃ₗ[R] (ι → R)
  frobeniusNormal :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p (graphIdeal h)

/-- Assemble the complete graph-centre certificate. -/
noncomputable def certificate (h : ι → R) : Certificate p h where
  proper := ReducedGraphCentreQuotient.graphIdeal_ne_top h
  finiteType := ReducedGraphCentreQuotient.graphIdeal_fg h
  quotient := ReducedGraphCentreQuotient.quotientEquiv h
  quotientReduced := ReducedGraphCentreQuotient.quotient_isReduced h
  quotientRegular := ReducedGraphCentreQuotient.quotient_isRegularRing h
  conormal := PolynomialGraphCentreCotangentBasis.cotangentEquivRows h
  frobeniusNormal :=
    ReducedPolynomialGraphCentreHeredity.graphIdeal_reflectsFrobeniusPowers p h

/-- Exact marked reflection exposed from the packaged certificate. -/
theorem power_mem_scaled_iff
    (h : ι → R) (e mark : Nat) (x : P (R := R) (ι := ι)) :
    x ^ (p ^ e) ∈ (graphIdeal h) ^ ((p ^ e) * mark) ↔
      x ∈ (graphIdeal h) ^ mark :=
  FrobeniusNormalCentre.power_mem_scaled_iff
    p (graphIdeal h) (certificate p h).frobeniusNormal e mark x

end

end ReducedRegularGraphCentreCertificate
end Experimental
end PCRLean
