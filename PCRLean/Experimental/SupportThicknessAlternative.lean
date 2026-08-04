import Mathlib
import PCRLean.Experimental.FiniteBadStratumCoverage

/-!
# The support-thickness alternative

Once a finite arrangement has been classified into clean and bad strata, the
bad layer has a second intrinsic dichotomy.

* `supportSingular`: the reduced support is not regular.  This is the carrier
  for lower-dimensional relative resolution and ambient lifting.
* `thicknessDefect`: the reduced support is regular, so the remaining failure
  is nilpotent thickness, non-quasi-regularity, conormal/Fitting defect, or an
  independent passive/boundary gate.

No arbitrary first bad stratum is selected: both finite sublayers are retained.
The file proves exact disjoint coverage only.  Geometric realization of the
relative word and strict thickness descent remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace SupportThicknessAlternative

noncomputable section

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Bad strata whose reduced support is still singular. -/
def supportSingularLayer
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] : Finset α :=
  bad.filter fun a => ¬ SupportRegular a

/-- Bad strata with regular reduced support; all remaining failure is assigned
  to the thickness/contact/Fitting or independent-legality chamber. -/
def thicknessLayer
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] : Finset α :=
  bad.filter SupportRegular

@[simp] theorem mem_supportSingularLayer_iff
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] (a : α) :
    a ∈ supportSingularLayer bad SupportRegular ↔
      a ∈ bad ∧ ¬ SupportRegular a := by
  simp [supportSingularLayer]

@[simp] theorem mem_thicknessLayer_iff
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] (a : α) :
    a ∈ thicknessLayer bad SupportRegular ↔
      a ∈ bad ∧ SupportRegular a := by
  simp [thicknessLayer]

/-- The two defect sublayers are disjoint. -/
theorem layers_disjoint
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] :
    Disjoint
      (supportSingularLayer bad SupportRegular)
      (thicknessLayer bad SupportRegular) := by
  rw [Finset.disjoint_left]
  intro a hs ht
  have hns := (mem_supportSingularLayer_iff bad SupportRegular a).mp hs
  have hr := (mem_thicknessLayer_iff bad SupportRegular a).mp ht
  exact hns.2 hr.2

/-- Every bad stratum belongs to exactly one of the two sublayers. -/
theorem union_layers
    (bad : Finset α) (SupportRegular : α → Prop)
    [DecidablePred SupportRegular] :
    supportSingularLayer bad SupportRegular ∪
      thicknessLayer bad SupportRegular = bad := by
  ext a
  by_cases hr : SupportRegular a <;> simp [supportSingularLayer,
    thicknessLayer, hr]

/-- Choice-free three-way coverage: clean arrangement, singular reduced
support, or regular-support thickness defect. -/
inductive Coverage
    (strata : Finset α)
    (Good SupportRegular : α → Prop)
    [DecidablePred Good] [DecidablePred SupportRegular] : Type u where
  | clean (allGood : ∀ a ∈ strata, Good a)
  | defect
      (badNonempty :
        (FiniteBadStratumCoverage.badStrata strata Good).Nonempty)
      (partition :
        supportSingularLayer
            (FiniteBadStratumCoverage.badStrata strata Good)
            SupportRegular ∪
          thicknessLayer
            (FiniteBadStratumCoverage.badStrata strata Good)
            SupportRegular =
          FiniteBadStratumCoverage.badStrata strata Good)

/-- Exact support-thickness classifier. -/
noncomputable def classify
    (strata : Finset α)
    (Good SupportRegular : α → Prop)
    [DecidablePred Good] [DecidablePred SupportRegular] :
    Coverage strata Good SupportRegular := by
  classical
  match FiniteBadStratumCoverage.classify strata Good with
  | .clean h => exact Coverage.clean h
  | .defect h =>
      exact Coverage.defect h
        (union_layers
          (FiniteBadStratumCoverage.badStrata strata Good)
          SupportRegular)

end

end SupportThicknessAlternative
end Experimental
end PCRLean
