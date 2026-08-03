import Mathlib
import PCRLean.ActualIdealGluing
import PCRLean.Experimental.PolynomialGraphCentreHeredity
import PCRLean.Experimental.PolynomialGraphCentreQuotient
import PCRLean.Experimental.PolynomialGraphBoundaryIntersection

/-!
# Nested polynomial graph hybrids flatten by triangular reduction

Let

`R = A[Y_j]`, `P = R[Z_i]`.

Assume the coefficient defect ideal is itself a graph ideal

`K_g = (Y_j-g_j) ⊂ R`

and the outer packet graph is

`Z_i-h_i(Y) = 0`.

Modulo `K_g`, every `h_i(Y)` equals its graph value `h_i(g)`.  Therefore

`K_g P + (Z_i-h_i(Y)) = K_g P + (Z_i-h_i(g))`.

The right-hand side is triangular: the inner graph equations and the outer
constant graph equations form one larger regular coordinate/graph centre after
flattening the iterated polynomial ring.  Thus a graph-valued coefficient
closure creates no new nonlinear all-chart obstruction.

This theorem is the first hereditary all-chart subchamber for a nonzero hybrid
defect.  General regular coefficient closures still require an étale graph
atlas and overlap descent.
-/

namespace PCRLean
namespace Experimental
namespace NestedPolynomialGraphHybrid

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
variable {δ : Type v} [Fintype δ] [DecidableEq δ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev R := MvPolynomial δ A
abbrev P := MvPolynomial ι (R (A := A) (δ := δ))

open PolynomialGraphCentreHeredity
open PolynomialGraphCentreQuotient
open PolynomialGraphBoundaryIntersection

/-- Inner coefficient graph ideal. -/
def innerIdeal (g : δ → A) : Ideal (R (A := A) (δ := δ)) :=
  graphIdeal g

/-- Extension of the inner graph ideal to the outer polynomial ring. -/
def extendedInnerIdeal (g : δ → A) :
    Ideal (P (A := A) (δ := δ) (ι := ι)) :=
  Ideal.map MvPolynomial.C (innerIdeal g)

/-- Evaluation of an outer graph coefficient on the inner graph. -/
def reducedCoefficient
    (g : δ → A) (h : ι → R (A := A) (δ := δ))
    (i : ι) : A :=
  graphEval g (h i)

/-- Constant lift of the reduced outer graph value back to the inner
coefficient ring. -/
def reducedOuterGraph
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) :
    ι → R (A := A) (δ := δ) :=
  fun i => MvPolynomial.C (reducedCoefficient g h i)

/-- Every outer coefficient differs from its reduced value by an inner graph
equation. -/
theorem coefficient_sub_reduced_mem_innerIdeal
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) (i : ι) :
    h i - reducedOuterGraph g h i ∈ innerIdeal g := by
  have hmem := sub_constantProjection_mem g (h i)
  simpa [PolynomialGraphCentreQuotient.constantProjection,
    reducedOuterGraph, reducedCoefficient] using hmem

/-- Outer graph generator with varying coefficient differs from the reduced
outer generator by an extended inner-graph element. -/
theorem graphGenerator_sub_reduced_mem_extendedInnerIdeal
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) (i : ι) :
    graphGenerator h i - graphGenerator (reducedOuterGraph g h) i ∈
      extendedInnerIdeal (ι := ι) g := by
  have hcoeff :
      MvPolynomial.C (h i - reducedOuterGraph g h i) ∈
        extendedInnerIdeal (ι := ι) g :=
    Ideal.mem_map_of_mem MvPolynomial.C
      (coefficient_sub_reduced_mem_innerIdeal g h i)
  have heq :
      graphGenerator h i - graphGenerator (reducedOuterGraph g h) i =
        -MvPolynomial.C (h i - reducedOuterGraph g h i) := by
    simp [graphGenerator]
    ring
  rw [heq]
  exact (extendedInnerIdeal (ι := ι) g).neg_mem hcoeff

/-- Original nested hybrid ideal. -/
def hybridIdeal
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) :
    Ideal (P (A := A) (δ := δ) (ι := ι)) :=
  graphIdeal h ⊔ extendedInnerIdeal (ι := ι) g

/-- Triangularly reduced nested hybrid ideal. -/
def reducedHybridIdeal
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) :
    Ideal (P (A := A) (δ := δ) (ι := ι)) :=
  graphIdeal (reducedOuterGraph g h) ⊔
    extendedInnerIdeal (ι := ι) g

/-- Each original outer graph generator belongs to the reduced hybrid ideal. -/
theorem original_generator_mem_reduced
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) (i : ι) :
    graphGenerator h i ∈ reducedHybridIdeal g h := by
  have hdiff := graphGenerator_sub_reduced_mem_extendedInnerIdeal g h i
  have hreduced :
      graphGenerator (reducedOuterGraph g h) i ∈ reducedHybridIdeal g h :=
    (show graphIdeal (reducedOuterGraph g h) ≤ reducedHybridIdeal g h
      from le_sup_left) (graphGenerator_mem _ i)
  have hdiff' :
      graphGenerator h i - graphGenerator (reducedOuterGraph g h) i ∈
        reducedHybridIdeal g h :=
    (show extendedInnerIdeal (ι := ι) g ≤ reducedHybridIdeal g h
      from le_sup_right) hdiff
  have hadd := (reducedHybridIdeal g h).add_mem hdiff' hreduced
  simpa using hadd

/-- Each reduced outer graph generator belongs to the original hybrid ideal. -/
theorem reduced_generator_mem_original
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) (i : ι) :
    graphGenerator (reducedOuterGraph g h) i ∈ hybridIdeal g h := by
  have hdiff := graphGenerator_sub_reduced_mem_extendedInnerIdeal g h i
  have horiginal : graphGenerator h i ∈ hybridIdeal g h :=
    (show graphIdeal h ≤ hybridIdeal g h from le_sup_left)
      (graphGenerator_mem h i)
  have hneg :
      -(graphGenerator h i - graphGenerator (reducedOuterGraph g h) i) ∈
        hybridIdeal g h :=
    (hybridIdeal g h).neg_mem
      ((show extendedInnerIdeal (ι := ι) g ≤ hybridIdeal g h
        from le_sup_right) hdiff)
  have hadd := (hybridIdeal g h).add_mem horiginal hneg
  simpa using hadd

/-- Main triangular reduction theorem. -/
theorem hybridIdeal_eq_reducedHybridIdeal
    (g : δ → A) (h : ι → R (A := A) (δ := δ)) :
    hybridIdeal g h = reducedHybridIdeal g h := by
  apply le_antisymm
  · apply sup_le
    · rw [graphIdeal, Ideal.span_le]
      rintro x ⟨i, rfl⟩
      exact original_generator_mem_reduced g h i
    · exact le_sup_right
  · apply sup_le
    · rw [graphIdeal, Ideal.span_le]
      rintro x ⟨i, rfl⟩
      exact reduced_generator_mem_original g h i
    · exact le_sup_right

/-- Exact quotient of the nested hybrid centre by the coefficient graph base. -/
noncomputable def quotientEquivInner :
    (P (A := A) (δ := δ) (ι := ι) ⧸ hybridIdeal g h) ≃+*
      (R (A := A) (δ := δ) ⧸ innerIdeal g) := by
  rw [hybridIdeal_eq_reducedHybridIdeal]
  exact PolynomialGraphBoundaryIntersection.quotientEquiv
    (reducedOuterGraph g h) (innerIdeal g)

/-- Complete quotient of the nested hybrid centre is the original passive
coefficient ring `A`. -/
noncomputable def quotientEquiv :
    (P (A := A) (δ := δ) (ι := ι) ⧸ hybridIdeal g h) ≃+* A :=
  (quotientEquivInner (g := g) (h := h)).trans
    (PolynomialGraphCentreQuotient.quotientEquiv g)

/-- Regularity of `A` transfers to the nested graph-hybrid centre. -/
theorem quotient_isRegularRing
    [IsRegularRing A] :
    IsRegularRing
      (P (A := A) (δ := δ) (ι := ι) ⧸ hybridIdeal g h) := by
  exact IsRegularRing.of_ringEquiv
    (quotientEquiv (g := g) (h := h)).symm

end

end NestedPolynomialGraphHybrid
end Experimental
end PCRLean
