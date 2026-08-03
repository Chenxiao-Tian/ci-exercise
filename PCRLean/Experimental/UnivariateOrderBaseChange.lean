import Mathlib
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import PCRLean.Experimental.UnivariateFrobeniusOrderHeredity

/-!
# Univariate order under faithful coefficient extension

An injective coefficient map preserves polynomial support, hence preserves the
trailing order.  Taylor translation commutes with coefficient maps, so marked
singularity at a rational point is preserved after extending the coefficient
field and mapping the point.

This proves the perfect-field-extension/base-change part of the local
one-variable Frobenius heredity chamber.  It does not address nonfaithful maps,
localization at arbitrary scheme points, several variables, or scheme-level
smooth base change.
-/

namespace PCRLean
namespace Experimental
namespace UnivariateOrderBaseChange

noncomputable section

universe u v

variable {K : Type u} {L : Type v}
variable [Field K] [Field L]

open UnivariateFrobeniusOrderHeredity

/-- Injective coefficient extension preserves trailing degree exactly. -/
theorem trailingDegree_map_eq
    (φ : K →+* L) (hφ : Function.Injective φ)
    (f : K[X]) :
    (f.map φ).trailingDegree = f.trailingDegree := by
  rw [Polynomial.trailingDegree, Polynomial.trailingDegree,
    Polynomial.support_map_of_injective f hφ]

/-- The natural-number trailing order is therefore also preserved. -/
theorem natTrailingDegree_map_eq
    (φ : K →+* L) (hφ : Function.Injective φ)
    (f : K[X]) :
    (f.map φ).natTrailingDegree = f.natTrailingDegree := by
  exact Polynomial.natTrailingDegree_eq_of_trailingDegree_eq
    (trailingDegree_map_eq φ hφ f)

/-- Marked singularity at the origin is invariant under faithful coefficient
extension. -/
theorem atOriginSingular_map_iff
    (φ : K →+* L) (hφ : Function.Injective φ)
    (f : K[X]) (mark : Nat) :
    AtOriginSingular (f.map φ) mark ↔ AtOriginSingular f mark := by
  rw [AtOriginSingular, AtOriginSingular,
    Polynomial.map_eq_zero_iff hφ,
    natTrailingDegree_map_eq φ hφ f]

/-- Taylor translation commutes with coefficient extension. -/
theorem taylor_map_eq
    (φ : K →+* L) (a : K) (f : K[X]) :
    Polynomial.taylor (φ a) (f.map φ) =
      (Polynomial.taylor a f).map φ := by
  exact (Polynomial.map_taylor f a φ).symm

/-- Pointwise marked singularity is invariant after mapping both the
coefficients and the rational point. -/
theorem atPointSingular_map_iff
    (φ : K →+* L) (hφ : Function.Injective φ)
    (a : K) (f : K[X]) (mark : Nat) :
    AtPointSingular (φ a) (f.map φ) mark ↔
      AtPointSingular a f mark := by
  unfold AtPointSingular
  rw [taylor_map_eq φ a f]
  exact atOriginSingular_map_iff φ hφ (Polynomial.taylor a f) mark

/-- The same base-change law for an indexed weighted presentation. -/
theorem family_atPointSingular_map_iff
    {κ : Type*}
    (φ : K →+* L) (hφ : Function.Injective φ)
    (a : K) (equation : κ → K[X]) (mark : κ → Nat) :
    (∀ j, AtPointSingular (φ a) ((equation j).map φ) (mark j)) ↔
      (∀ j, AtPointSingular a (equation j) (mark j)) := by
  constructor
  · intro h j
    exact (atPointSingular_map_iff φ hφ a (equation j) (mark j)).mp (h j)
  · intro h j
    exact (atPointSingular_map_iff φ hφ a (equation j) (mark j)).mpr (h j)

end

end UnivariateOrderBaseChange
end Experimental
end PCRLean
