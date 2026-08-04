import Mathlib
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# Intrinsic minimality of a module-section order ideal

For an arbitrary module section `x : P`, define its intrinsic order ideal by
all values `f x` with `f : P →ₗ[R] R`.  The ideal is the least coefficient
ideal that absorbs every such dual value.  This minimality theorem and the unit
obstruction no-go require no basis, no finite-projectivity hypothesis, and no
chosen dual frame.

The final theorem records the exact boundary: if all dual functionals vanish on
a nonzero section, then its order ideal is zero although the section is not.
Consequently `orderIdeal x = ⊥ → x = 0` is not available without a separate
dual-separation certificate.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicOrderIdealMinimalityAtomic

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]

open ProjectiveSectionOrderIdeal

/-- Every intrinsic dual coefficient vanishes modulo `J`. -/
def FunctionalsVanishMod (x : P) (J : Ideal R) : Prop :=
  ∀ f : P →ₗ[R] R, f x ∈ J

/-- The intrinsic vanishing predicate is exactly ideal containment. -/
theorem functionalsVanishMod_iff_orderIdeal_le
    (x : P) (J : Ideal R) :
    FunctionalsVanishMod x J ↔ orderIdeal x ≤ J := by
  constructor
  · intro h
    rw [orderIdeal, Ideal.span_le]
    rintro a ⟨f, rfl⟩
    exact h f
  · intro h f
    exact h (Ideal.subset_span ⟨f, rfl⟩)

/-- The order ideal is the least coefficient ideal absorbing every dual value. -/
theorem orderIdeal_isLeast_intrinsic (x : P) :
    IsLeast {J : Ideal R | FunctionalsVanishMod x J} (orderIdeal x) := by
  constructor
  · intro f
    exact Ideal.subset_span ⟨f, rfl⟩
  · intro J hJ
    exact (functionalsVanishMod_iff_orderIdeal_le x J).mp hJ

/-- Unit-obstruction no-go: no proper coefficient ideal absorbs all dual values
when the intrinsic order ideal is the unit ideal. -/
theorem no_proper_ideal_absorbs_unit_intrinsic
    (x : P) (htop : orderIdeal x = ⊤) :
    ¬ ∃ J : Ideal R, J ≠ ⊤ ∧ FunctionalsVanishMod x J := by
  rintro ⟨J, hproper, hJ⟩
  apply hproper
  apply top_unique
  rw [← htop]
  exact (functionalsVanishMod_iff_orderIdeal_le x J).mp hJ

/-- Exact converse form of the unit-obstruction no-go. -/
theorem orderIdeal_eq_top_iff_no_proper_intrinsic
    (x : P) :
    orderIdeal x = ⊤ ↔
      ¬ ∃ J : Ideal R, J ≠ ⊤ ∧ FunctionalsVanishMod x J := by
  constructor
  · exact no_proper_ideal_absorbs_unit_intrinsic x
  · intro h
    by_contra htop
    apply h
    refine ⟨orderIdeal x, htop, ?_⟩
    intro f
    exact Ideal.subset_span ⟨f, rfl⟩

/-- If every dual functional vanishes on `x`, the order ideal is zero. -/
theorem orderIdeal_eq_bot_of_all_functionals_zero
    (x : P) (h : ∀ f : P →ₗ[R] R, f x = 0) :
    orderIdeal x = ⊥ := by
  apply le_antisymm
  · rw [orderIdeal, Ideal.span_le]
    rintro a ⟨f, rfl⟩
    rw [h f]
    exact Ideal.zero_mem ⊥
  · exact bot_le

/-- Counterexample schema isolating the missing dual-separation hypothesis. -/
theorem zeroDetection_requires_dual_separation
    (x : P) (hx : x ≠ 0)
    (hdual : ∀ f : P →ₗ[R] R, f x = 0) :
    orderIdeal x = ⊥ ∧ x ≠ 0 := by
  exact ⟨orderIdeal_eq_bot_of_all_functionals_zero x hdual, hx⟩

end

end IntrinsicOrderIdealMinimalityAtomic
end Experimental
end PCRLean
