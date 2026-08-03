import Mathlib
import PCRLean.Experimental.PolynomialGraphBlowupHeredity

/-!
# Universal framed charts for polynomial graph blowups, repaired version

This module gives a proof-producing universal property for the explicit graph
blowup chart.  It supersedes the first experimental draft by separating the
single key residual calculation from the composition proof.

For `r_i = Z_i-h_i`, a target map `ψ` and ratios `u_i` satisfying

`ψ(r_i)=ψ(r_k)u_i`,  `u_k=1`,

the standard graph chart uniquely maps to the target with exceptional
coordinate `ψ(r_k)` and nonpivot ratio coordinates `u_i`.  The resulting map
composed with the source graph-chart map is exactly `ψ`.

This is the affine universal property with a chosen pivot and chosen ratios.
It remains to identify overlap localizations and to package the charts into the
scheme blowup/Proj construction.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBlowupChartUniversalV2

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]
variable {C : Type w} [CommRing C] [Algebra R C]

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity

abbrev P := MvPolynomial ι R

/-- The existing explicit graph chart map as an `R`-algebra homomorphism. -/
def graphChartAlgHom (h : ι → R) (k : ι) :
    P (R := R) (ι := ι) →ₐ[R] P :=
  { graphChartMap h k with
    commutes' := by
      intro r
      simp [graphChartMap, coordinateChartMap, translate] }

/-- Ambient coordinates are the graph equations plus their coefficient values. -/
theorem X_eq_graphGenerator_add_C
    (h : ι → R) (i : ι) :
    (MvPolynomial.X i : P (R := R) (ι := ι)) =
      graphGenerator h i + MvPolynomial.C (h i) := by
  simp [graphGenerator]

/-- Direct coordinate formula for the graph chart. -/
theorem graphChartAlgHom_X
    (h : ι → R) (k i : ι) :
    graphChartAlgHom h k (MvPolynomial.X i) =
      exceptional (R := R) k *
          explicitRootTransform (R := R) k i +
        MvPolynomial.C (h i) := by
  rw [X_eq_graphGenerator_add_C h i, map_add,
    graphGenerator_factorization]
  simp [graphChartAlgHom]

/-- Assignment of the target chart variables. -/
def chartAssignment
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) (i : ι) : C :=
  if i = k then ψ (graphGenerator h k) else ratio i

/-- Canonical map from the chart polynomial ring. -/
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

/-- The exceptional coordinate maps to the pivot graph equation. -/
theorem chartLift_exceptional
    (h : ι → R) (k : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C) :
    chartLift h k ψ ratio (exceptional (R := R) k) =
      ψ (graphGenerator h k) := by
  simp [exceptional, chartAssignment]

/-- Every explicit controlled root maps to the prescribed ratio, including the
pivot residual after using `ratio k = 1`. -/
theorem chartLift_explicitRootTransform
    (h : ι → R) (k i : ι)
    (ψ : P (R := R) (ι := ι) →ₐ[R] C)
    (ratio : ι → C)
    (hratioPivot : ratio k = 1) :
    chartLift h k ψ ratio
        (explicitRootTransform (R := R) k i) = ratio i := by
  by_cases hki : i = k
  · subst i
    simp [explicitRootTransform, hratioPivot]
  · simp [explicitRootTransform, chartAssignment, hki]

/-- The canonical chart lift factors the source map. -/
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
  rw [AlgHom.comp_apply, graphChartAlgHom_X, map_add, map_mul,
    chartLift_exceptional,
    chartLift_explicitRootTransform h k i ψ ratio hratioPivot,
    ← hfactor i]
  rw [← map_add, ← X_eq_graphGenerator_add_C h i]

/-- Uniqueness from the values of the exceptional and nonpivot ratio variables. -/
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
    simp [chartLift, chartAssignment, hki]
  · intro F hF
    exact chartLift_unique h k ψ ratio F hF.2.1 hF.2.2

end

end PolynomialGraphBlowupChartUniversalV2
end Experimental
end PCRLean
