import Mathlib
import PCRLean.Experimental.ProjectiveMoritaDescent
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# Minimality of the projective section order ideal

A finite dual frame gives a coordinate-free criterion for a section `x : P` to
vanish modulo an ideal `J`: every frame coefficient `F_i(x)` lies in `J`.
Because the frame coefficients generate the intrinsic order ideal, this
condition is equivalent to

`orderIdeal(x) ≤ J`.

Consequently the order ideal is the smallest defect ideal compatible with the
section.  In particular, if `orderIdeal(x) = ⊤`, no proper ideal can absorb all
obstruction coefficients.  This is the rigorous unit-obstruction no-go needed
by the hybrid-centre compiler: the unit case cannot be hidden as a legal proper
centre and must trigger terminality or an earlier strict drop.
-/

namespace PCRLean
namespace Experimental
namespace ProjectiveSectionOrderIdealMinimality

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal

/-- Frame-coordinate formulation of vanishing modulo an ideal. -/
def CoefficientsVanishMod
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R) : Prop :=
  ∀ i : ι, F.functional i x ∈ J

/-- Every frame coefficient belongs to the intrinsic order ideal. -/
theorem coefficientsVanishMod_orderIdeal
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) :
    CoefficientsVanishMod F x (orderIdeal x) := by
  intro i
  exact Ideal.subset_span ⟨F.functional i, rfl⟩

/-- Main minimality theorem: coefficientwise vanishing modulo `J` is exactly
containment of the intrinsic order ideal in `J`. -/
theorem coefficientsVanishMod_iff_orderIdeal_le
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R) :
    CoefficientsVanishMod F x J ↔ orderIdeal x ≤ J := by
  constructor
  · intro h
    rw [← F.frameOrderIdeal_eq_orderIdeal x,
      frameOrderIdeal, Ideal.span_le]
    rintro a ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (Ideal.subset_span ⟨F.functional i, rfl⟩)

/-- The order ideal is the least ideal satisfying the frame-coordinate
vanishing condition. -/
theorem orderIdeal_isLeast
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) :
    IsLeast {J : Ideal R | CoefficientsVanishMod F x J}
      (orderIdeal x) := by
  constructor
  · exact coefficientsVanishMod_orderIdeal F x
  · intro J hJ
    exact (coefficientsVanishMod_iff_orderIdeal_le F x J).mp hJ

/-- Unit obstruction no-go: if the order ideal is the unit ideal, every ideal
absorbing all obstruction coefficients is itself the unit ideal. -/
theorem eq_top_of_orderIdeal_eq_top_of_coefficientsVanishMod
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R)
    (htop : orderIdeal x = ⊤)
    (hJ : CoefficientsVanishMod F x J) :
    J = ⊤ := by
  apply top_unique
  rw [← htop]
  exact (coefficientsVanishMod_iff_orderIdeal_le F x J).mp hJ

/-- Equivalent no-go form for proper ideals. -/
theorem no_proper_ideal_absorbs_unit_obstruction
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P)
    (htop : orderIdeal x = ⊤) :
    ¬ ∃ J : Ideal R,
      J ≠ ⊤ ∧ CoefficientsVanishMod F x J := by
  rintro ⟨J, hproper, hJ⟩
  exact hproper
    (eq_top_of_orderIdeal_eq_top_of_coefficientsVanishMod
      F x J htop hJ)

/-- Conversely, if no proper ideal absorbs the coefficients, the order ideal
must be the unit ideal. -/
theorem orderIdeal_eq_top_iff_no_proper_absorbing_ideal
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (x : P) :
    orderIdeal x = ⊤ ↔
      ¬ ∃ J : Ideal R,
        J ≠ ⊤ ∧ CoefficientsVanishMod F x J := by
  constructor
  · exact no_proper_ideal_absorbs_unit_obstruction F x
  · intro h
    by_contra htop
    apply h
    exact ⟨orderIdeal x, htop,
      coefficientsVanishMod_orderIdeal F x⟩

end

end ProjectiveSectionOrderIdealMinimality
end Experimental
end PCRLean
