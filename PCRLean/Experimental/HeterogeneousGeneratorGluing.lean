import Mathlib
import PCRLean.ActualIdealGluing

/-!
# Gluing finite generator frames of different sizes

Two local presentations of the same ideal need not have the same number of
named equations.  This module generalizes the existing generator-change theorem
to finite index types `μ` and `ι` of different cardinalities.

If every `g_a` is a finite linear combination of the `h_i`, then `(g) ≤ (h)`.
Mutual combination certificates give equality.  No square matrix, determinant,
or chosen basis is required.

This is the appropriate interface between a global finite module presentation
and locally minimal graph/conormal frames.
-/

namespace PCRLean
namespace Experimental
namespace HeterogeneousGeneratorGluing

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {μ : Type v} {ι : Type w}
variable [Fintype μ] [Fintype ι]

/-- A heterogeneous finite-combination certificate gives ideal inclusion. -/
theorem generatedIdeal_le_of_combinations
    (g : μ → R) (h : ι → R)
    (coeff : μ → ι → R)
    (hcomb : ∀ a, g a = ∑ i, coeff a i * h i) :
    ActualIdealGluing.generatedIdeal g ≤
      ActualIdealGluing.generatedIdeal h := by
  rw [ActualIdealGluing.generatedIdeal,
    ActualIdealGluing.generatedIdeal, Ideal.span_le]
  rintro x ⟨a, rfl⟩
  rw [hcomb a]
  exact (Ideal.span (Set.range h)).sum_mem fun i _ =>
    (Ideal.span (Set.range h)).mul_mem_left (coeff a i)
      (Ideal.subset_span ⟨i, rfl⟩)

/-- Mutual heterogeneous combination certificates give exact ideal equality. -/
theorem generatedIdeal_eq_of_mutual_combinations
    (g : μ → R) (h : ι → R)
    (forward : μ → ι → R)
    (backward : ι → μ → R)
    (hforward : ∀ a, g a = ∑ i, forward a i * h i)
    (hbackward : ∀ i, h i = ∑ a, backward i a * g a) :
    ActualIdealGluing.generatedIdeal g =
      ActualIdealGluing.generatedIdeal h := by
  apply le_antisymm
  · exact generatedIdeal_le_of_combinations g h forward hforward
  · exact generatedIdeal_le_of_combinations h g backward hbackward

/-- Typed equivalence of two finite frames of possibly different sizes. -/
structure FrameEquivalence (g : μ → R) (h : ι → R) where
  forward : μ → ι → R
  backward : ι → μ → R
  reconstruct_g : ∀ a, g a = ∑ i, forward a i * h i
  reconstruct_h : ∀ i, h i = ∑ a, backward i a * g a

namespace FrameEquivalence

variable {g : μ → R} {h : ι → R}

/-- Equivalent heterogeneous frames define the same actual ideal. -/
theorem ideal_eq (E : FrameEquivalence g h) :
    ActualIdealGluing.generatedIdeal g =
      ActualIdealGluing.generatedIdeal h := by
  exact generatedIdeal_eq_of_mutual_combinations
    g h E.forward E.backward E.reconstruct_g E.reconstruct_h

end FrameEquivalence

end

end HeterogeneousGeneratorGluing
end Experimental
end PCRLean
