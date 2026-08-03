import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Tower
import PCRLean.Experimental.SplitSurjectionSymmetricQuotient

/-!
# Experimental arbitrary base change of split-surjection centres

A split linear quotient remains split after arbitrary scalar extension.  More
strongly, because the kernel is the image of an explicit residual projection,
its kernel commutes with every base change, not merely flat base change:

`ker (A ⊗ project) = A ⊗ ker project`.

Consequently the intrinsic actual centre after base change is generated exactly
by the base-changed kernel.  This is the algebraic localization theorem needed
for gluing Fitting-minor charts.  It does not yet identify the symmetric
algebra after scalar extension with the scalar extension of the original
symmetric algebra, or prove scheme-level descent of ideal sheaves.
-/

namespace PCRLean
namespace Experimental
namespace SplitSurjectionBaseChange

noncomputable section

universe uR uA uV uW

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [CommRing A] [Algebra R A]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

open SplitSurjectionSymmetricQuotient

variable (S : SplitSurjection (R := R) (V := V) (Kmod := W))

/-- Scalar extension of a split surjection. -/
noncomputable def baseChange :
    SplitSurjection
      (R := A)
      (V := TensorProduct R A V)
      (Kmod := TensorProduct R A W) where
  project := LinearMap.baseChange A S.project
  liftBack := LinearMap.baseChange A S.liftBack
  rightInverse := by
    calc
      (LinearMap.baseChange A S.project).comp
          (LinearMap.baseChange A S.liftBack) =
        LinearMap.baseChange A (S.project.comp S.liftBack) := by
          simpa using
            (LinearMap.baseChange_comp
              (A := A) S.liftBack S.project).symm
      _ = LinearMap.baseChange A LinearMap.id := by
        rw [S.rightInverse]
      _ = LinearMap.id := LinearMap.baseChange_id

/-- Pointwise form of the base-changed right inverse. -/
@[simp] theorem baseChange_project_liftBack
    (y : TensorProduct R A W) :
    (S.baseChange (A := A)).project
        ((S.baseChange (A := A)).liftBack y) = y := by
  exact (S.baseChange (A := A)).project_liftBack y

/-- Original residual projection as a linear endomorphism. -/
def residualLinear : V →ₗ[R] V :=
  LinearMap.id - S.liftBack.comp S.project

@[simp] theorem residualLinear_apply (x : V) :
    S.residualLinear x = S.residual x := by
  rfl

/-- The residual projection lands in the original kernel. -/
theorem residualLinear_mem_ker (x : V) :
    S.residualLinear x ∈ LinearMap.ker S.project := by
  simpa [residualLinear_apply] using S.residual_mem_ker x

/-- Base change commutes with the residual projector. -/
theorem baseChange_residualLinear :
    LinearMap.baseChange A S.residualLinear =
      (S.baseChange (A := A)).residualLinear := by
  rw [residualLinear, residualLinear]
  simp only [LinearMap.baseChange_sub, LinearMap.baseChange_id]
  rw [LinearMap.baseChange_comp]
  rfl

/-- Pure tensors of residual directions transform as expected. -/
theorem baseChange_residual_tmul (a : A) (x : V) :
    (S.baseChange (A := A)).residual (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] S.residual x := by
  change (S.baseChange (A := A)).residualLinear (a ⊗ₜ[R] x) = _
  rw [← S.baseChange_residualLinear (A := A)]
  simp

/-- Every base-changed residual lies in the scalar extension of the original
kernel. -/
theorem baseChange_residual_mem
    (z : TensorProduct R A V) :
    (S.baseChange (A := A)).residual z ∈
      Submodule.baseChange A (LinearMap.ker S.project) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [SplitSurjection.residual]
  | tmul a x =>
      rw [S.baseChange_residual_tmul (A := A)]
      exact Submodule.tmul_mem_baseChange_of_mem
        a (S.residual_mem_ker x)
  | add x y hx hy =>
      have hadd :
          (S.baseChange (A := A)).residual (x + y) =
            (S.baseChange (A := A)).residual x +
              (S.baseChange (A := A)).residual y := by
        simp [SplitSurjection.residual]
      rw [hadd]
      exact (Submodule.baseChange A
        (LinearMap.ker S.project)).add_mem hx hy

/-- The kernel of a split map commutes with arbitrary base change.  No flatness
hypothesis on `A` is required. -/
theorem ker_baseChange_eq :
    LinearMap.ker (LinearMap.baseChange A S.project) =
      Submodule.baseChange A (LinearMap.ker S.project) := by
  apply le_antisymm
  · intro z hz
    have hzero : LinearMap.baseChange A S.project z = 0 :=
      LinearMap.mem_ker.mp hz
    have hres : (S.baseChange (A := A)).residual z = z := by
      simp [SplitSurjection.residual, baseChange, hzero]
    rw [← hres]
    exact S.baseChange_residual_mem (A := A) z
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hxzero : S.project x = 0 := LinearMap.mem_ker.mp hx
    simp [hxzero]

/-- The intrinsic actual centre after scalar extension is generated exactly by
the base-changed kernel. -/
theorem baseChangedKernelIdeal_eq :
    (S.baseChange (A := A)).kernelIdeal =
      Ideal.span (Set.range fun x :
        Submodule.baseChange A (LinearMap.ker S.project) =>
          SymmetricAlgebra.ι A (TensorProduct R A V) x.1) := by
  unfold SplitSurjectionSymmetricQuotient.SplitSurjection.kernelIdeal
  rw [S.ker_baseChange_eq (A := A)]

/-- Every pure tensor of an original kernel direction contributes a generator
of the base-changed actual centre. -/
theorem pureKernelGenerator_mem
    (a : A) (x : LinearMap.ker S.project) :
    SymmetricAlgebra.ι A (TensorProduct R A V) (a ⊗ₜ[R] x.1) ∈
      (S.baseChange (A := A)).kernelIdeal := by
  apply Ideal.subset_span
  refine ⟨⟨a ⊗ₜ[R] x.1, ?_⟩, rfl⟩
  apply LinearMap.mem_ker.mpr
  have hxzero : S.project x.1 = 0 := LinearMap.mem_ker.mp x.2
  simp [baseChange, hxzero]

/-- Exact quotient theorem after arbitrary scalar extension. -/
noncomputable def quotientEquiv :
    (SymmetricAlgebra A (TensorProduct R A V) ⧸
        (S.baseChange (A := A)).kernelIdeal) ≃+*
      SymmetricAlgebra A (TensorProduct R A W) :=
  (S.baseChange (A := A)).quotientEquiv

end

end SplitSurjectionBaseChange
end Experimental
end PCRLean
