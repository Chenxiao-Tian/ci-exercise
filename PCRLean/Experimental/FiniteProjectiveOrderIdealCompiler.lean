import Mathlib
import PCRLean.Experimental.FiniteProjectivePresentationDualFrame
import PCRLean.Experimental.ProjectiveSectionOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealMinimality
import PCRLean.Experimental.ProjectiveSectionOrderIdealBaseChange

/-!
# Automatic order-ideal theorems from finite-projective presentations

The intrinsic order ideal is defined using all linear functionals, hence is
independent of a presentation. A split finite-free presentation supplies the
finite dual frame required by the finite proofs. This file packages zero
detection, minimality, the unit-obstruction no-go theorem, and compatible base
change without asking the caller to provide a frame separately.
-/

namespace PCRLean
namespace Experimental
namespace FiniteProjectiveOrderIdealCompiler

noncomputable section

universe u v w x y

open FiniteProjectivePresentationDualFrame
open ProjectiveSectionOrderIdeal
open ProjectiveSectionOrderIdealMinimality

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Coefficientwise vanishing expressed directly in a split presentation. -/
def SplitCoefficientsVanishMod
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R) : Prop :=
  ∀ i : ι, F.section x i ∈ J

/-- Presentation coefficients generate exactly the intrinsic order ideal. -/
theorem coefficientsVanishMod_iff_orderIdeal_le
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (x : P) (J : Ideal R) :
    SplitCoefficientsVanishMod F x J ↔ orderIdeal x ≤ J := by
  simpa [SplitCoefficientsVanishMod] using
    ProjectiveSectionOrderIdealMinimality.coefficientsVanishMod_iff_orderIdeal_le
      F.toDualFrame x J

/-- The intrinsic order ideal is least among coefficient defects in the split
presentation. -/
theorem orderIdeal_isLeast
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (x : P) :
    IsLeast {J : Ideal R | SplitCoefficientsVanishMod F x J}
      (orderIdeal x) := by
  simpa [SplitCoefficientsVanishMod] using
    ProjectiveSectionOrderIdealMinimality.orderIdeal_isLeast F.toDualFrame x

/-- Zero order ideal detects the zero section. -/
theorem orderIdeal_eq_bot_iff
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (x : P) :
    orderIdeal x = ⊥ ↔ x = 0 :=
  ProjectiveSectionOrderIdeal.orderIdeal_eq_bot_iff F.toDualFrame x

/-- Unit-obstruction no-go in split-presentation coordinates. -/
theorem no_proper_ideal_absorbs_unit_section
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (x : P)
    (htop : orderIdeal x = ⊤) :
    ¬ ∃ J : Ideal R,
      J ≠ ⊤ ∧ SplitCoefficientsVanishMod F x J := by
  simpa [SplitCoefficientsVanishMod] using
    ProjectiveSectionOrderIdealMinimality.no_proper_ideal_absorbs_unit_obstruction
      F.toDualFrame x htop

section BaseChange

variable {S : Type x} [CommRing S] [Algebra R S]
variable {Q : Type y} [AddCommGroup Q]
variable [Module R Q] [Module S Q] [IsScalarTower R S Q]

/-- Two split finite-free presentations with coefficient-compatible sections. -/
structure CompatibleSplitPresentations
    (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))
    (G : SplitFiniteFreePresentation (R := S) (P := Q) (ι := ι)) where
  map : P →ₗ[R] Q
  section_coordinate : ∀ i x,
    G.section (map x) i = algebraMap R S (F.section x i)

namespace CompatibleSplitPresentations

variable
  {F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι)}
  {G : SplitFiniteFreePresentation (R := S) (P := Q) (ι := ι)}
  (C : CompatibleSplitPresentations F G)

/-- Derived dual frames satisfy the existing compatibility interface. -/
def toCompatibleFrames :
    ProjectiveSectionOrderIdealBaseChange.CompatibleFrames
      F.toDualFrame G.toDualFrame where
  map := C.map
  coefficient i x := by
    simpa using C.section_coordinate i x

/-- Exact order-ideal transport for compatible split presentations. -/
theorem map_orderIdeal_eq (x : P) :
    Ideal.map (algebraMap R S) (orderIdeal x) =
      orderIdeal (C.map x) :=
  ProjectiveSectionOrderIdealBaseChange.CompatibleFrames.map_orderIdeal_eq
    C.toCompatibleFrames x

/-- Faithful flatness reflects the proper-nonzero hybrid regime. -/
theorem properNonzero_iff
    [Module.FaithfullyFlat R S]
    (x : P) :
    (orderIdeal (C.map x) ≠ ⊥ ∧ orderIdeal (C.map x) ≠ ⊤) ↔
      (orderIdeal x ≠ ⊥ ∧ orderIdeal x ≠ ⊤) :=
  ProjectiveSectionOrderIdealBaseChange.CompatibleFrames.properNonzero_iff
    C.toCompatibleFrames x

end CompatibleSplitPresentations
end BaseChange

end

end FiniteProjectiveOrderIdealCompiler
end Experimental
end PCRLean
