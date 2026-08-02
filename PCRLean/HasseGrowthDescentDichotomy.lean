import Mathlib
import PCRLean.HasseSaturationDescent

/-!
# Strict Hasse growth versus Frobenius descent

For a seed ideal on a monogenic Frobenius frame there are only two algebraic
possibilities.  If the seed is already stable under the finite transported
Hasse packet, it descends exactly from the Frobenius base.  Otherwise canonical
Hasse saturation strictly enlarges it.  Adding the unit-ideal case gives a
three-way transition suitable for a Noetherian termination compiler:

* terminal unit saturation;
* proper Frobenius descent;
* strict memory growth.

This theorem is local and algebraic.  A global resolution program must still
transport the same ancestor memory through blowup charts and prove that the
descended core yields a regular jointly permissible centre.
-/

namespace PCRLean
namespace HasseGrowthDescentDichotomy

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable {q : Nat} {t : R}

abbrev Frame := MonogenicFrobeniusFrame.Frame

/-- Stability gives exact descent of the seed itself. -/
theorem eq_coreExtension_of_stable
    (F : Frame (R := R) (A := A) q t)
    (I : Ideal A)
    (hstable : DifferentialIdealSaturation.Stable
      (HasseSaturationDescent.transportedHasseAddHom F) I) :
    I = (HasseSaturationDescent.frobeniusCore F I).map
      (algebraMap R A) := by
  have hfix : HasseSaturationDescent.hasseSaturation F I = I :=
    DifferentialIdealSaturation.saturation_eq_self_of_stable
      (HasseSaturationDescent.transportedHasseAddHom F) I hstable
  calc
    I = HasseSaturationDescent.hasseSaturation F I := hfix.symm
    _ = (HasseSaturationDescent.frobeniusCore F I).map
        (algebraMap R A) :=
      HasseSaturationDescent.hasseSaturation_eq_map_core F I

/-- Exact local dichotomy: either the seed descends, or its canonical Hasse
closure is a strict enlargement. -/
theorem descent_or_strict_growth
    (F : Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    I = (HasseSaturationDescent.frobeniusCore F I).map
        (algebraMap R A) ∨
      I < HasseSaturationDescent.hasseSaturation F I := by
  by_cases hstable : DifferentialIdealSaturation.Stable
      (HasseSaturationDescent.transportedHasseAddHom F) I
  · exact Or.inl (eq_coreExtension_of_stable F I hstable)
  · exact Or.inr
      (HasseSaturationDescent.lt_hasseSaturation_of_not_stable
        F I hstable)

/-- A proper stable seed descends from a proper base ideal. -/
theorem proper_core_of_stable
    (F : Frame (R := R) (A := A) q t)
    (I : Ideal A) (hI : I ≠ ⊤)
    (hstable : DifferentialIdealSaturation.Stable
      (HasseSaturationDescent.transportedHasseAddHom F) I) :
    HasseSaturationDescent.frobeniusCore F I ≠ ⊤ := by
  intro hcore
  apply hI
  calc
    I = (HasseSaturationDescent.frobeniusCore F I).map
        (algebraMap R A) :=
      eq_coreExtension_of_stable F I hstable
    _ = ⊤ := by simp [hcore]

/-- Three-way local transition theorem: unit ideal, proper Frobenius descent,
or strict Hasse-memory growth. -/
theorem terminal_or_proper_descent_or_growth
    (F : Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    I = ⊤ ∨
      (∃ J : Ideal R,
        J ≠ ⊤ ∧ I = J.map (algebraMap R A)) ∨
      I < HasseSaturationDescent.hasseSaturation F I := by
  by_cases htop : I = ⊤
  · exact Or.inl htop
  · by_cases hstable : DifferentialIdealSaturation.Stable
        (HasseSaturationDescent.transportedHasseAddHom F) I
    · exact Or.inr (Or.inl
        ⟨HasseSaturationDescent.frobeniusCore F I,
          proper_core_of_stable F I htop hstable,
          eq_coreExtension_of_stable F I hstable⟩)
    · exact Or.inr (Or.inr
        (HasseSaturationDescent.lt_hasseSaturation_of_not_stable
          F I hstable))

end

end HasseGrowthDescentDichotomy
end PCRLean
