import Mathlib
import PCRLean.Experimental.ProjectiveMoritaDescent
import PCRLean.Experimental.ProjectiveSectionOrderIdeal
import PCRLean.Experimental.ProjectiveSectionOrderIdealBaseChange
import PCRLean.Experimental.IntrinsicOrderIdealMinimality

/-!
# Split finite-free presentations and finite dual frames

A finite dual frame and a retraction from a finite free module encode the same
constructive certificate.  This file formalizes both directions needed by the
X031 order-ideal compiler.

The forward direction is the load-bearing bridge: from

`(ι → R) --project--> P --section--> (ι → R)`

with `project ∘ section = id`, it constructs a finite dual frame on `P`.  Hence
the intrinsic order ideal detects zero and can be transported by the existing
compatible-frame base-change theorems.

No global basis is chosen and no claim is made that every finite-projective
module comes with a canonical splitting.  Construction of a finite split
presentation on a Fitting chart remains a separate geometric obligation.
-/

namespace PCRLean
namespace Experimental
namespace SplitFreePresentationDualFrame

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal

/-- An explicit retraction of a finite free module onto `P`. -/
structure SplitFreePresentation where
  project : (ι → R) →ₗ[R] P
  section : P →ₗ[R] (ι → R)
  rightInverse : project.comp section = LinearMap.id

namespace SplitFreePresentation

variable (S : SplitFreePresentation (R := R) (P := P) (ι := ι))

/-- Coordinate evaluation on the finite free module. -/
def coordinate (i : ι) : (ι → R) →ₗ[R] R where
  toFun a := a i
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro r a
    rfl

/-- The frame vector obtained by projecting the `i`th standard vector. -/
def vector (i : ι) : P :=
  S.project (Pi.single i 1)

/-- The frame functional obtained from the `i`th coordinate of the section. -/
def functional (i : ι) : P →ₗ[R] R :=
  (coordinate (R := R) i).comp S.section

/-- Pointwise form of the retraction identity. -/
@[simp] theorem project_section (x : P) :
    S.project (S.section x) = x := by
  have h := congrArg (fun f : P →ₗ[R] P => f x) S.rightInverse
  simpa [LinearMap.comp_apply] using h

/-- Standard finite-coordinate reconstruction. -/
theorem sum_smul_single (a : ι → R) :
    (∑ i : ι, (a i) • Pi.single i (1 : R)) = a := by
  classical
  ext j
  simp [Pi.single_apply]

/-- The projected standard vectors and section coordinates reconstruct every
point of `P`. -/
theorem reconstruct (x : P) :
    (∑ i : ι, (S.functional i x) • S.vector i) = x := by
  calc
    (∑ i : ι, (S.functional i x) • S.vector i) =
        S.project (∑ i : ι, (S.section x i) • Pi.single i (1 : R)) := by
      simp [functional, coordinate, vector]
    _ = S.project (S.section x) := by
      rw [S.sum_smul_single]
    _ = x := S.project_section x

/-- Canonical finite dual frame attached to the split finite-free
presentation. -/
def dualFrame : DualFrame (R := R) (P := P) (ι := ι) where
  vector := S.vector
  functional := S.functional
  reconstruct := S.reconstruct

/-- A split presentation makes the intrinsic order ideal zero-detecting. -/
theorem orderIdeal_eq_bot_iff (x : P) :
    orderIdeal x = ⊥ ↔ x = 0 :=
  ProjectiveSectionOrderIdeal.orderIdeal_eq_bot_iff S.dualFrame x

/-- The finite coefficient ideal from the constructed frame is exactly the
intrinsic order ideal. -/
theorem frameOrderIdeal_eq_orderIdeal (x : P) :
    frameOrderIdeal S.dualFrame x = orderIdeal x :=
  ProjectiveSectionOrderIdeal.frameOrderIdeal_eq_orderIdeal S.dualFrame x

/-- Two split finite-free presentations of the same module give the same
coefficient ideal. -/
theorem frameOrderIdeal_independent
    (T : SplitFreePresentation (R := R) (P := P) (ι := ι))
    (x : P) :
    frameOrderIdeal S.dualFrame x = frameOrderIdeal T.dualFrame x := by
  rw [S.frameOrderIdeal_eq_orderIdeal, T.frameOrderIdeal_eq_orderIdeal]

end SplitFreePresentation

/-- Linear map from finite coordinates associated to a dual frame. -/
def projectOfDualFrame
    (F : DualFrame (R := R) (P := P) (ι := ι)) :
    (ι → R) →ₗ[R] P where
  toFun a := ∑ i : ι, (a i) • F.vector i
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp [mul_smul]

/-- Coordinate section associated to a dual frame. -/
def sectionOfDualFrame
    (F : DualFrame (R := R) (P := P) (ι := ι)) :
    P →ₗ[R] (ι → R) where
  toFun x i := F.functional i x
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro r x
    ext i
    simp

/-- Every finite dual frame gives an explicit split finite-free presentation. -/
def splitFreePresentationOfDualFrame
    (F : DualFrame (R := R) (P := P) (ι := ι)) :
    SplitFreePresentation (R := R) (P := P) (ι := ι) where
  project := projectOfDualFrame F
  section := sectionOfDualFrame F
  rightInverse := by
    apply LinearMap.ext
    intro x
    change (∑ i : ι, (F.functional i x) • F.vector i) = x
    exact F.reconstruct x

section BaseChange

universe uS vQ

variable {Sring : Type uS} [CommRing Sring] [Algebra R Sring]
variable {Q : Type vQ} [AddCommGroup Q]
variable [Module R Q] [Module Sring Q] [IsScalarTower R Sring Q]

/-- Compatibility of two split finite-free presentations with one section map.
The condition is exactly coefficientwise compatibility of the two sections. -/
structure CompatibleSplitPresentations
    (A : SplitFreePresentation (R := R) (P := P) (ι := ι))
    (B : SplitFreePresentation (R := Sring) (P := Q) (ι := ι)) where
  map : P →ₗ[R] Q
  sectionCoefficient : ∀ i x,
    B.section (map x) i = algebraMap R Sring (A.section x i)

namespace CompatibleSplitPresentations

variable
  {A : SplitFreePresentation (R := R) (P := P) (ι := ι)}
  {B : SplitFreePresentation (R := Sring) (P := Q) (ι := ι)}
  (C : CompatibleSplitPresentations A B)

/-- Compatible split presentations automatically produce the compatible dual
frames required by the existing base-change theorem. -/
def compatibleFrames :
    ProjectiveSectionOrderIdealBaseChange.CompatibleFrames
      A.dualFrame B.dualFrame where
  map := C.map
  coefficient := by
    intro i x
    simpa [SplitFreePresentation.dualFrame,
      SplitFreePresentation.functional,
      SplitFreePresentation.coordinate] using C.sectionCoefficient i x

/-- Exact base change of the intrinsic order ideal. -/
theorem map_orderIdeal_eq (x : P) :
    Ideal.map (algebraMap R Sring) (orderIdeal x) =
      orderIdeal (C.map x) :=
  C.compatibleFrames.map_orderIdeal_eq x

/-- Zero detection is faithfully-flat local for compatible split
presentations. -/
theorem orderIdeal_eq_bot_iff
    [Module.FaithfullyFlat R Sring]
    (x : P) :
    orderIdeal (C.map x) = ⊥ ↔ orderIdeal x = ⊥ :=
  C.compatibleFrames.orderIdeal_eq_bot_iff x

/-- Unit obstruction is faithfully-flat local for compatible split
presentations. -/
theorem orderIdeal_eq_top_iff
    [Module.FaithfullyFlat R Sring]
    (x : P) :
    orderIdeal (C.map x) = ⊤ ↔ orderIdeal x = ⊤ :=
  C.compatibleFrames.orderIdeal_eq_top_iff x

/-- The genuine proper-nonzero hybrid branch is faithfully-flat local. -/
theorem properNonzero_iff
    [Module.FaithfullyFlat R Sring]
    (x : P) :
    (orderIdeal (C.map x) ≠ ⊥ ∧ orderIdeal (C.map x) ≠ ⊤) ↔
      (orderIdeal x ≠ ⊥ ∧ orderIdeal x ≠ ⊤) :=
  C.compatibleFrames.properNonzero_iff x

end CompatibleSplitPresentations

end BaseChange

end

end SplitFreePresentationDualFrame
end Experimental
end PCRLean
