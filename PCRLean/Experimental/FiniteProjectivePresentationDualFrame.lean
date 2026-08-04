import Mathlib
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Projective
import PCRLean.Experimental.ProjectiveMoritaDescent

/-!
# Finite-projective presentations produce finite dual frames

A finite free presentation equipped with a linear retraction produces an
explicit finite dual frame on the target. If the target is projective, every
surjective finite free presentation splits by the projective lifting property,
so the dual frame is constructed rather than assumed as separate input.

This is an experimental local-algebra bridge for D001/FND-11. It does not
construct the finite presentation from an arbitrary resolution state and does
not prove the later regular-centre, owner, boundary, hereditary, termination,
or globalization gates.
-/

namespace PCRLean
namespace Experimental
namespace FiniteProjectivePresentationDualFrame

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent

/-- A finite free presentation together with a chosen linear section. -/
structure SplitFiniteFreePresentation where
  project : (ι → R) →ₗ[R] P
  section : P →ₗ[R] (ι → R)
  retract : project.comp section = LinearMap.id

namespace SplitFiniteFreePresentation

variable (F : SplitFiniteFreePresentation (R := R) (P := P) (ι := ι))

/-- Pointwise form of the retraction identity. -/
@[simp] theorem project_section (x : P) :
    F.project (F.section x) = x := by
  have h := congrArg (fun L : P →ₗ[R] P => L x) F.retract
  simpa [LinearMap.comp_apply] using h

/-- The presentation map is surjective. -/
theorem project_surjective : Function.Surjective F.project := by
  intro x
  exact ⟨F.section x, F.project_section x⟩

/-- A split finite-free presentation makes the target projective. -/
theorem projective : Module.Projective R P := by
  letI : Module.Projective R (ι → R) := inferInstance
  exact Module.Projective.of_split F.section F.project F.retract

/-- The finite dual frame induced from the standard basis of the free module. -/
def toDualFrame : DualFrame (R := R) (P := P) (ι := ι) where
  vector i := F.project (Pi.basisFun R ι i)
  functional i := ((Pi.basisFun R ι).coord i).comp F.section
  reconstruct x := by
    calc
      (∑ i, (((Pi.basisFun R ι).coord i).comp F.section) x •
          F.project (Pi.basisFun R ι i)) =
          F.project (F.section x) := by
        rw [← (Pi.basisFun R ι).sum_repr (F.section x), map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul]
        simp [LinearMap.comp_apply]
      _ = x := F.project_section x

@[simp] theorem toDualFrame_vector (i : ι) :
    F.toDualFrame.vector i = F.project (Pi.basisFun R ι i) := rfl

@[simp] theorem toDualFrame_functional_apply (i : ι) (x : P) :
    F.toDualFrame.functional i x = F.section x i := by
  simp [toDualFrame, LinearMap.comp_apply]

/-- The derived frame reconstructs every target section. -/
theorem toDualFrame_reconstruct (x : P) :
    (∑ i : ι, F.toDualFrame.functional i x • F.toDualFrame.vector i) = x :=
  F.toDualFrame.reconstruct x

end SplitFiniteFreePresentation

/-- A surjective finite free presentation of a projective module admits a
linear section. -/
noncomputable def ofProjectiveSurjection
    [Module.Projective R P]
    (project : (ι → R) →ₗ[R] P)
    (hproject : Function.Surjective project) :
    SplitFiniteFreePresentation (R := R) (P := P) (ι := ι) := by
  have hrange : project.range = ⊤ := LinearMap.range_eq_top.mpr hproject
  obtain ⟨section, hsection⟩ :=
    LinearMap.exists_rightInverse_of_surjective project hrange
  exact ⟨project, section, hsection⟩

/-- Automatic finite dual frame from projectivity and a surjective finite-free
presentation. -/
noncomputable def dualFrameOfProjectiveSurjection
    [Module.Projective R P]
    (project : (ι → R) →ₗ[R] P)
    (hproject : Function.Surjective project) :
    DualFrame (R := R) (P := P) (ι := ι) :=
  (ofProjectiveSurjection project hproject).toDualFrame

/-- Existence form of the automatic dual-frame bridge. -/
theorem exists_dualFrame_of_projective_surjection
    [Module.Projective R P]
    (project : (ι → R) →ₗ[R] P)
    (hproject : Function.Surjective project) :
    ∃ F : DualFrame (R := R) (P := P) (ι := ι),
      ∀ x : P, (∑ i : ι, F.functional i x • F.vector i) = x := by
  refine ⟨dualFrameOfProjectiveSurjection project hproject, ?_⟩
  intro x
  exact (dualFrameOfProjectiveSurjection project hproject).reconstruct x

end

end FiniteProjectivePresentationDualFrame
end Experimental
end PCRLean
