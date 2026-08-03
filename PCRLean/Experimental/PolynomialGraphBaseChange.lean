import Mathlib
import PCRLean.Experimental.PolynomialGraphCentreHeredity

/-!
# Exact base change of polynomial graph centres

For a ring homomorphism `f : R →+* S`, coefficientwise polynomial base change
sends the graph ideal

`(Z_i-h_i) ⊂ R[Z_i]`

exactly to

`(Z_i-f(h_i)) ⊂ S[Z_i]`.

This is the algebraic descent law needed on localization overlaps. It is an
equality of actual ideals, not merely equality of their supports or quotient
rings.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBaseChange

noncomputable section

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable {ι : Type w} [DecidableEq ι]

open PolynomialGraphCentreHeredity

/-- Base-changed graph tuple. -/
def mapGraph (f : R →+* S) (h : ι → R) : ι → S :=
  fun i => f (h i)

/-- Coefficientwise map on the polynomial ambient ring. -/
def polynomialMap (f : R →+* S) :
    MvPolynomial ι R →+* MvPolynomial ι S :=
  MvPolynomial.map f

@[simp] theorem polynomialMap_graphGenerator
    (f : R →+* S) (h : ι → R) (i : ι) :
    polynomialMap (ι := ι) f (graphGenerator h i) =
      graphGenerator (mapGraph f h) i := by
  simp [polynomialMap, graphGenerator, mapGraph]

/-- Main exact base-change law for graph ideals. -/
theorem map_graphIdeal_eq
    (f : R →+* S) (h : ι → R) :
    Ideal.map (polynomialMap (ι := ι) f) (graphIdeal h) =
      graphIdeal (mapGraph f h) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, graphIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap, polynomialMap_graphGenerator]
    exact graphGenerator_mem (mapGraph f h) i
  · rw [graphIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem
      (polynomialMap (ι := ι) f) (graphGenerator_mem h i)
    simpa using hm

/-- Pointwise equal base-changed graph tuples give equal extended ideals. -/
theorem map_graphIdeal_eq_of_pointwise
    (f : R →+* S) (h : ι → R) (g : ι → S)
    (heq : ∀ i, f (h i) = g i) :
    Ideal.map (polynomialMap (ι := ι) f) (graphIdeal h) =
      graphIdeal g := by
  rw [map_graphIdeal_eq]
  apply congrArg graphIdeal
  funext i
  exact heq i

end

end PolynomialGraphBaseChange
end Experimental
end PCRLean
