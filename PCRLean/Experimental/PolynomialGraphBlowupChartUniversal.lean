import Mathlib
import PCRLean.Experimental.PolynomialGraphBlowupHeredity

/-!
# Universal framed charts for polynomial graph blowups

For the graph centre

`r_i = Z_i - h_i`

in `R[Z_i]`, the standard chart with pivot `k` is again the polynomial ring
`R[E,U_i]`, encoded using the same variable type: `Z_k` denotes the exceptional
parameter `E`, while `Z_i` for `i ≠ k` denotes the ratio `U_i`.

The source map is

`r_k ↦ E`,  `r_i ↦ E U_i`.

This file proves the corresponding universal property with the chart frame
made explicit.  Given any `R`-algebra map `ψ` and ratios `u_i` satisfying

`ψ(r_i) = ψ(r_k) u_i`,  `u_k = 1`,

there is a canonical map from the chart polynomial ring to the target which
sends `E` to `ψ(r_k)` and `U_i` to `u_i`; its composition with the graph chart
map is exactly `ψ`.  The map is unique among maps with those values on the
chart variables.

This theorem identifies the existing explicit chart map with the usual framed
affine blowup chart presentation.  It does not yet construct scheme `Proj`,
prove overlap localization, or show compatibility with arbitrary base change.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBlowupChartUniversal

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]
variable {C : Type w} [CommRing C] [Algebra R C]

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity

abbrev P := MvPolynomial ι R

/-- The explicit graph chart map as an `R`-algebra homomorphism. -/
def graphChartAlgHom (h : ι → R) (k : ι) :
    P (R := R) (ι := ι) →ₐ[R] P :=
  { graphChartMap h k with
    commutes' := by
      intro r
      simp [graphChartMap, coordinateChartMap, translate] }

/-- The direct formula for the image of one ambient coordinate. -/
theorem graphChartAlgHom_X
    (h : ι → R) (k i : ι) :
    graphChartAlgHom h k (MvPolynomial.X i) =
      exceptional (R := R) k *
          explicitRootTransform (R := R) k i +
        MvPolynomial.C (h i) := by
  have hdecomp :
      (MvPolynomial.X i : P (R := R) (ι := ι)) =
        graphGenerator h i + MvPolynomial.C (h i) := by
    simp [graphGenerator]
  rw [hdecomp, map_add, graphGenerator_factorization]
  simp [graphChartAlgHom]

/-- Assignment of the chart variables in a target algebra. -/
def chartAssignment
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) (i : ι) : C :=
  if i = k then ψ (graphGenerator h k) else ratio i

/-- Canonical map from the framed chart polynomial ring. -/
def chartLift
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) :
    P (R := R) (ι := ι) →ₐ[R] C :=
  MvPolynomial.aeval (chartAssignment h k ψ ratio)

@[simp] theorem chartLift_X
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) (i : ι) :
    chartLift h k ψ ratio (MvPolynomial.X i) =
      chartAssignment h k ψ ratio i := by
  simp [chartLift]

/-- The chart lift sends the exceptional coordinate to the pivot graph
 equation. -/
theorem chartLift_exceptional
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) :
    chartLift h k ψ ratio (exceptional (R := R) k) =
      ψ (graphGenerator h k) := by
  simp [exceptional, chartAssignment]

/-- Nonpivot chart variables are sent to the prescribed ratios. -/
theorem chartLift_nonpivot
    (h : ι → R) (k i : ι) (hki : i ≠ k)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) :
    chartLift h k ψ ratio (MvPolynomial.X i) = ratio i := by
  simp [chartAssignment, hki]

/-- Universal factorization through the framed graph blowup chart. -/
theorem chartLift_comp_graphChart
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C)
    (hratioPivot : ratio k = 1)
    (hfactor : ∀ i : ι,
      ψ (graphGenerator h i) =
        ψ (graphGenerator h k) * ratio i) :
    (chartLift h k ψ ratio).comp (graphChartAlgHom h k) = ψ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, graphChartAlgHom_X, map_add, map_mul]
  by_cases hki : i = k
  · subst i
    simp [chartLift, chartAssignment, hratioPivot, hfactor]
  · simp [chartLift, chartAssignment, hki, hfactor]

/-- Uniqueness of the framed chart lift from its values on the exceptional and
 ratio coordinates. -/
theorem chartLift_unique
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C)
    (F : P (R := R) (ι := ι) →ₐ[R] C)
    (hFpivot : F (exceptional (R := R) k) =
      ψ (graphGenerator h k))
    (hFratio : ∀ i : ι, i ≠ k → F (MvPolynomial.X i) = ratio i) :
    F = chartLift h k ψ ratio := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hki : i = k
  · subst i
    simpa [exceptional, chartAssignment] using hFpivot
  · simpa [chartAssignment, hki] using hFratio i hki

/-- Existential-unique universal property of the framed chart. -/
theorem existsUnique_chartLift
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C)
    (hratioPivot : ratio k = 1)
    (hfactor : ∀ i : ι,
      ψ (graphGenerator h i) =
        ψ (graphGenerator h k) * ratio i) :
    ∃! F : P (R := R) (ι := ι) →ₐ[R] C,
      F.comp (graphChartAlgHom h k) = ψ ∧
      F (exceptional (R := R) k) = ψ (graphGenerator h k) ∧
      ∀ i : ι, i ≠ k → F (MvPolynomial.X i) = ratio i := by
  refine ⟨chartLift h k ψ ratio, ?_, ?_⟩
  · refine ⟨chartLift_comp_graphChart h k ψ ratio
      hratioPivot hfactor,
      chartLift_exceptional h k ψ ratio, ?_⟩
    intro i hki
    exact chartLift_nonpivot h k i hki ψ ratio
  · intro F hF
    exact chartLift_unique h k ψ ratio F hF.2.1 hF.2.2

end

end PolynomialGraphBlowupChartUniversal
end Experimental
end PCRLean
