import Mathlib
import PCRLean.Experimental.PolynomialGraphCentreQuotient
import PCRLean.Experimental.PolynomialGraphBlowupHeredity

/-!
# Complete local certificate for polynomial graph centres

For a polynomial graph centre `Z_i - h_i = 0` over a Noetherian regular domain,
this module packages the current local algebra into one typed certificate:

* an actual ideal;
* properness and non-whole-centre strictness;
* finite generation;
* an exact quotient by the coefficient ring and regularity of the centre;
* Frobenius-normality of the centre filtration;
* marked permissibility of the full prime-power root packet; and
* explicit terminality on every standard blowup chart.

This is a strong affine local chamber theorem.  It is not yet a scheme-level
regular-immersion theorem, does not include passive Tor safety or boundary SNC,
and does not reconstruct the next differential packet after arbitrary
cleaning, normalization or overlap descent.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphFrobeniusCentreCertificate

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open PolynomialGraphCentreHeredity
open PolynomialGraphCentreQuotient
open PolynomialGraphBlowupHeredity

abbrev P := MvPolynomial ι R

/-- A graph equation is nonzero. -/
theorem graphGenerator_ne_zero
    (h : ι → R) (i : ι) :
    graphGenerator h i ≠ 0 := by
  intro hz
  have ht := congrArg (translate h) hz
  have hx : (MvPolynomial.X i : P (R := R) (ι := ι)) = 0 := by
    simpa using ht
  have hXne : (MvPolynomial.X i : P (R := R) (ι := ι)) ≠ 0 := by
    simp [MvPolynomial.X]
  exact hXne hx

/-- A nonempty graph packet cuts out a proper closed subset of the ambient
space, rather than the whole ambient space. -/
theorem graphIdeal_ne_bot
    (h : ι → R) : graphIdeal h ≠ ⊥ := by
  intro hbot
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hm : graphGenerator h i ∈ graphIdeal h := graphGenerator_mem h i
  have hz : graphGenerator h i = 0 := by
    simpa [hbot] using hm
  exact graphGenerator_ne_zero h i hz

variable [IsNoetherianRing R] [IsRegularRing R]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Full local certificate for the graph centre at Frobenius level `p^e`. -/
structure Certificate (h : ι → R) (e : Nat) where
  centre : Ideal (P (R := R) (ι := ι))
  centre_eq : centre = graphIdeal h
  proper : centre ≠ ⊤
  nonwhole : centre ≠ ⊥
  finiteType : centre.FG
  quotient : (P (R := R) (ι := ι) ⧸ centre) ≃+* R
  quotientRegular : IsRegularRing (P (R := R) (ι := ι) ⧸ centre)
  frobeniusNormal : FrobeniusNormalCentre.ReflectsFrobeniusPowers p centre
  sourcePermissible :
    MarkedIdeal.Permissible
      (R := P (R := R) (ι := ι))
      ⟨sourceIdeal h (p ^ e), p ^ e,
        pow_pos (Fact.out : p.Prime).pos e⟩
      centre
  allChartsTerminal : ∀ k : ι,
    transformedRootIdeal (R := R) k (p ^ e) = ⊤
  rootFactorization : ∀ k i : ι,
    graphChartMap h k ((graphGenerator h i) ^ (p ^ e)) =
      (exceptional (R := R) k) ^ (p ^ e) *
        (explicitRootTransform (R := R) k i) ^ (p ^ e)

/-- Assemble the complete local graph-centre certificate. -/
noncomputable def certificate
    (h : ι → R) (e : Nat) : Certificate p h e where
  centre := graphIdeal h
  centre_eq := rfl
  proper := graphIdeal_ne_top h
  nonwhole := graphIdeal_ne_bot h
  finiteType := graphIdeal_fg h
  quotient := PolynomialGraphCentreQuotient.quotientEquiv h
  quotientRegular := PolynomialGraphCentreQuotient.quotient_isRegularRing h
  frobeniusNormal := graphIdeal_reflectsFrobeniusPowers p h
  sourcePermissible := sourcePacket_permissible h
    (pow_pos (Fact.out : p.Prime).pos e)
  allChartsTerminal := fun k => transformedRootIdeal_eq_top
    (R := R) k (p ^ e)
  rootFactorization := fun k i => graphGenerator_pow_factorization
    h k i (p ^ e)

end

end PolynomialGraphFrobeniusCentreCertificate
end Experimental
end PCRLean
