import Mathlib
import PCRLean.Experimental.ProjectiveSectionOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealMinimality

/-!
# Intrinsic minimality of a module section order ideal

The order ideal of a section `x : P` is defined using every linear functional
`P →ₗ[R] R`.  Its minimality therefore does not require a basis, a dual frame,
finite projectivity, or a chosen presentation.

A finite dual frame remains useful as a finite certificate: frame-coordinate
vanishing is equivalent to intrinsic functional vanishing.  The distinction is
load-bearing for the X031 cokernel compiler.  Minimality and the unit-obstruction
no-go are unconditional; detection of `x = 0` from `orderIdeal x = ⊥` still
requires a dual-separation certificate such as a split finite-free presentation.
-/

namespace PCRLean
namespace Experimental
namespace IntrinsicOrderIdealMinimality

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal
open ProjectiveSectionOrderIdealMinimality

/-- Intrinsic vanishing of every dual coefficient modulo an ideal. -/
def FunctionalsVanishMod (x : P) (J : Ideal R) : Prop :=
  ∀ f : P →ₗ[R] R, f x ∈ J

/-- Every intrinsic functional value belongs to the order ideal. -/
theorem functionalsVanishMod_orderIdeal (x : P) :
    FunctionalsVanishMod x (orderIdeal x) := by
  intro f
  exact Ideal.subset_span ⟨f, rfl⟩

/-- Intrinsic functional vanishing modulo `J` is exactly containment of the
order ideal in `J`. -/
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

/-- The order ideal is the least coefficient ideal absorbing all intrinsic dual
values of the section. -/
theorem orderIdeal_isLeast_intrinsic (x : P) :
    IsLeast {J : Ideal R | FunctionalsVanishMod x J} (orderIdeal x) := by
  constructor
  · exact functionalsVanishMod_orderIdeal x
  · intro J hJ
    exact (functionalsVanishMod_iff_orderIdeal_le x J).mp hJ

/-- If the intrinsic order ideal is the unit ideal, every ideal absorbing all
dual coefficients is the unit ideal. -/
theorem eq_top_of_orderIdeal_eq_top_of_functionalsVanishMod
    (x : P) (J : Ideal R)
    (htop : orderIdeal x = ⊤)
    (hJ : FunctionalsVanishMod x J) :
    J = ⊤ := by
  apply top_unique
  rw [← htop]
  exact (functionalsVanishMod_iff_orderIdeal_le x J).mp hJ

/-- Intrinsic unit-obstruction no-go: no proper coefficient ideal absorbs every
dual value when the order ideal is the unit ideal. -/
theorem no_proper_ideal_absorbs_unit_intrinsic
    (x : P) (htop : orderIdeal x = ⊤) :
    ¬ ∃ J : Ideal R, J ≠ ⊤ ∧ FunctionalsVanishMod x J := by
  rintro ⟨J, hproper, hJ⟩
  exact hproper
    (eq_top_of_orderIdeal_eq_top_of_functionalsVanishMod x J htop hJ)

/-- Conversely, failure of every proper absorbing ideal is equivalent to the
unit order ideal. -/
theorem orderIdeal_eq_top_iff_no_proper_intrinsic
    (x : P) :
    orderIdeal x = ⊤ ↔
      ¬ ∃ J : Ideal R, J ≠ ⊤ ∧ FunctionalsVanishMod x J := by
  constructor
  · exact no_proper_ideal_absorbs_unit_intrinsic x
  · intro h
    by_contra htop
    apply h
    exact ⟨orderIdeal x, htop, functionalsVanishMod_orderIdeal x⟩

/-- A finite dual frame is a finite certificate for the intrinsic vanishing
predicate; it does not define a different ideal. -/
theorem frameCoefficients_iff_allFunctionals
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R) :
    CoefficientsVanishMod F x J ↔ FunctionalsVanishMod x J := by
  rw [coefficientsVanishMod_iff_orderIdeal_le,
    functionalsVanishMod_iff_orderIdeal_le]

/-- Boundary theorem: if all functionals vanish on `x`, then its order ideal is
zero.  Without a dual-separation hypothesis this need not force `x = 0`. -/
theorem orderIdeal_eq_bot_of_all_functionals_zero
    (x : P) (h : ∀ f : P →ₗ[R] R, f x = 0) :
    orderIdeal x = ⊥ := by
  apply le_antisymm
  · rw [orderIdeal, Ideal.span_le]
    rintro a ⟨f, rfl⟩
    simpa [h f]
  · exact bot_le

/-- Abstract counterexample schema showing exactly why zero detection requires
a dual-separation certificate. -/
theorem zeroDetection_requires_dual_separation
    (x : P) (hx : x ≠ 0)
    (hdual : ∀ f : P →ₗ[R] R, f x = 0) :
    orderIdeal x = ⊥ ∧ x ≠ 0 := by
  exact ⟨orderIdeal_eq_bot_of_all_functionals_zero x hdual, hx⟩

end

end IntrinsicOrderIdealMinimality
end Experimental
end PCRLean
