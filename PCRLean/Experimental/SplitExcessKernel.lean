import Mathlib
import Mathlib.Algebra.Module.Projective

/-!
# Split excess kernels are projective

For a surjective conormal map between finite projective modules, projectivity
of the target supplies a section.  The resulting excess kernel is then a
direct summand of the source and hence projective.  This is the precise local
algebra behind clean excess intersections: nonzero excess is compatible with
regular geometry whenever the conormal map is a split surjection.

No scheme-level regular-intersection or wonderful-blowup theorem is asserted
here.  Those require sheafification, regular-immersion hypotheses, all
intersection strata, owner legality, passive safety, boundary SNC, and
ordinary blowup serialization.
-/

namespace PCRLean
namespace Experimental
namespace SplitExcessKernel

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [AddCommGroup A] [Module R A]
variable {B : Type w} [AddCommGroup B] [Module R B]

/-- A linear surjection together with a chosen right inverse. -/
structure SplitSurjection where
  project : A →ₗ[R] B
  section : B →ₗ[R] A
  rightInverse : project.comp section = LinearMap.id

namespace SplitSurjection

variable (S : SplitSurjection (R := R) (A := A) (B := B))

/-- Pointwise form of the right-inverse identity. -/
@[simp] theorem project_section (b : B) :
    S.project (S.section b) = b := by
  have h := LinearMap.congr_fun S.rightInverse b
  simpa [LinearMap.comp_apply] using h

/-- The idempotent projector from the source onto the excess kernel. -/
def kernelProjector : A →ₗ[R] A :=
  LinearMap.id - S.section.comp S.project

/-- The projector lands in the kernel. -/
@[simp] theorem project_kernelProjector (a : A) :
    S.project (S.kernelProjector a) = 0 := by
  simp [kernelProjector, LinearMap.comp_apply]

/-- The projector as a retraction valued in the kernel subtype. -/
def kernelRetraction : A →ₗ[R] LinearMap.ker S.project where
  toFun a := ⟨S.kernelProjector a, by
    exact LinearMap.mem_ker.mpr (S.project_kernelProjector a)⟩
  map_add' x y := by
    apply Subtype.ext
    exact S.kernelProjector.map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact S.kernelProjector.map_smul r x

/-- The kernel retraction fixes every kernel element. -/
theorem kernelRetraction_comp_subtype :
    S.kernelRetraction.comp (LinearMap.ker S.project).subtype =
      LinearMap.id := by
  ext x
  apply Subtype.ext
  have hx : S.project (x : A) = 0 := LinearMap.mem_ker.mp x.property
  simp [kernelRetraction, kernelProjector, LinearMap.comp_apply, hx]

/-- A split excess kernel is a direct summand of the source; therefore it is
projective whenever the source is projective. -/
theorem kernel_projective
    [Module.Projective R A] :
    Module.Projective R (LinearMap.ker S.project) :=
  Module.Projective.of_split
    (LinearMap.ker S.project).subtype
    S.kernelRetraction
    S.kernelRetraction_comp_subtype

end SplitSurjection

/-- A surjection onto a projective target automatically becomes a split
surjection. -/
noncomputable def splitOfProjectiveTarget
    [Module.Projective R B]
    (q : A →ₗ[R] B) (hq : Function.Surjective q) :
    SplitSurjection (R := R) (A := A) (B := B) := by
  have hrange : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hq
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q hrange
  exact ⟨q, s, hs⟩

/-- The kernel of a surjection between projective modules is projective.  In
intersection theory this is applied to the conormal surjection; its kernel is
the clean excess module. -/
theorem kernel_projective_of_surjective
    [Module.Projective R A] [Module.Projective R B]
    (q : A →ₗ[R] B) (hq : Function.Surjective q) :
    Module.Projective R (LinearMap.ker q) := by
  let S := splitOfProjectiveTarget q hq
  exact S.kernel_projective

end

end SplitExcessKernel
end Experimental
end PCRLean
