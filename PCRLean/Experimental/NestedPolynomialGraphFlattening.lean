import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import PCRLean.Experimental.NestedPolynomialGraphHybrid
import PCRLean.Experimental.PolynomialGraphBlowupHeredity

/-!
# Flattening a nested graph hybrid to one graph centre

For

`P = A[Y_δ][Z_ι]`

and a nested hybrid centre

`(Y_d-g_d, Z_i-h_i(Y))`,

the triangular reduction first replaces `h_i(Y)` by `h_i(g)`.  The standard
iterated-polynomial equivalence

`A[Y_δ][Z_ι] ≃ A[Z_ι, Y_δ]`

then carries the reduced hybrid ideal exactly to the graph ideal of the single
tuple

`c(inl i) = h_i(g)`, `c(inr d) = g_d`.

Therefore the nested hybrid centre inherits the complete standard graph-centre
blowup atlas.  In particular, the full prime-power packet of its flattened
graph generators is terminal on every pivot chart.
-/

namespace PCRLean
namespace Experimental
namespace NestedPolynomialGraphFlattening

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] [IsDomain A]
variable {δ : Type v} [Fintype δ] [DecidableEq δ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open NestedPolynomialGraphHybrid
open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity

abbrev Inner := MvPolynomial δ A
abbrev Iterated := MvPolynomial ι (Inner (A := A) (δ := δ))
abbrev Flat := MvPolynomial (ι ⊕ δ) A

/-- Flattening equivalence from the iterated ring to one polynomial ring. -/
noncomputable def flatten :
    Iterated (A := A) (δ := δ) (ι := ι) ≃ₐ[A]
      Flat (A := A) (δ := δ) (ι := ι) :=
  (MvPolynomial.sumAlgEquiv A ι δ).symm

@[simp] theorem flatten_X (i : ι) :
    flatten (A := A) (δ := δ) (ι := ι) (MvPolynomial.X i) =
      MvPolynomial.X (Sum.inl i) := by
  exact MvPolynomial.iterToSum_X A ι δ i

@[simp] theorem flatten_C_X (d : δ) :
    flatten (A := A) (δ := δ) (ι := ι)
        (MvPolynomial.C (MvPolynomial.X d)) =
      MvPolynomial.X (Sum.inr d) := by
  exact MvPolynomial.iterToSum_C_X A ι δ d

@[simp] theorem flatten_C_C (a : A) :
    flatten (A := A) (δ := δ) (ι := ι)
        (MvPolynomial.C (MvPolynomial.C a)) =
      MvPolynomial.C a := by
  exact MvPolynomial.iterToSum_C_C A ι δ a

/-- One larger graph tuple after triangular reduction and flattening. -/
def combinedGraph
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ)) :
    (ι ⊕ δ) → A
  | Sum.inl i => reducedCoefficient g h i
  | Sum.inr d => g d

/-- Flattening sends every reduced outer graph equation to its combined graph
equation. -/
theorem flatten_reducedOuterGenerator
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ)) (i : ι) :
    flatten (A := A) (δ := δ) (ι := ι)
        (graphGenerator (reducedOuterGraph g h) i) =
      graphGenerator (combinedGraph g h) (Sum.inl i) := by
  simp [graphGenerator, reducedOuterGraph, combinedGraph]

/-- Flattening sends an extended inner graph equation to the corresponding
combined graph equation. -/
theorem flatten_innerGenerator
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ)) (d : δ) :
    flatten (A := A) (δ := δ) (ι := ι)
        (MvPolynomial.C (graphGenerator g d)) =
      graphGenerator (combinedGraph g h) (Sum.inr d) := by
  simp [graphGenerator, combinedGraph]

/-- Image of the reduced nested hybrid is exactly one graph ideal. -/
theorem map_reducedHybridIdeal_eq_graphIdeal
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ)) :
    Ideal.map (flatten (A := A) (δ := δ) (ι := ι))
        (reducedHybridIdeal g h) =
      graphIdeal (combinedGraph g h) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · rw [graphIdeal, Ideal.span_le]
      rintro x ⟨i, rfl⟩
      rw [Ideal.mem_comap, flatten_reducedOuterGenerator]
      exact graphGenerator_mem _ _
    · rw [extendedInnerIdeal, Ideal.map_le_iff_le_comap,
        innerIdeal, graphIdeal, Ideal.span_le]
      rintro x ⟨d, rfl⟩
      rw [Ideal.mem_comap, Ideal.mem_comap,
        RingHom.comp_apply, flatten_innerGenerator]
      exact graphGenerator_mem _ _
  · rw [graphIdeal, Ideal.span_le]
    rintro x ⟨s, rfl⟩
    cases s with
    | inl i =>
        rw [← flatten_reducedOuterGenerator g h i]
        apply Ideal.mem_map_of_mem
        exact (show graphIdeal (reducedOuterGraph g h) ≤
            reducedHybridIdeal g h from le_sup_left)
          (graphGenerator_mem _ i)
    | inr d =>
        rw [← flatten_innerGenerator g h d]
        apply Ideal.mem_map_of_mem
        exact (show extendedInnerIdeal (ι := ι) g ≤
            reducedHybridIdeal g h from le_sup_right)
          (Ideal.mem_map_of_mem MvPolynomial.C
            (graphGenerator_mem g d))

/-- Image of the original nonlinear nested hybrid is the same flattened graph
ideal. -/
theorem map_hybridIdeal_eq_graphIdeal
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ)) :
    Ideal.map (flatten (A := A) (δ := δ) (ι := ι))
        (hybridIdeal g h) =
      graphIdeal (combinedGraph g h) := by
  rw [hybridIdeal_eq_reducedHybridIdeal]
  exact map_reducedHybridIdeal_eq_graphIdeal g h

/-- The flattened full controlled root packet is terminal on every standard
pivot chart. -/
theorem flattened_transformedRootIdeal_eq_top
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ))
    (k : ι ⊕ δ) (q : Nat) :
    transformedRootIdeal (R := A) k q = ⊤ :=
  transformedRootIdeal_eq_top (R := A) k q

/-- Pairwise agreement of all terminal flattened chart packets. -/
theorem flattened_transformedRootIdeal_eq
    (g : δ → A) (h : ι → Inner (A := A) (δ := δ))
    (i j : ι ⊕ δ) (q : Nat) :
    transformedRootIdeal (R := A) i q =
      transformedRootIdeal (R := A) j q :=
  transformedRootIdeal_eq (R := A) i j q

end

end NestedPolynomialGraphFlattening
end Experimental
end PCRLean
