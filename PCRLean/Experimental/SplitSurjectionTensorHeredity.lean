import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Map
import PCRLean.Experimental.SplitSurjectionRegularCentre

/-!
# Experimental tensor heredity of split-surjection centres

A split conormal projection remains split after tensoring with an arbitrary
module. No flatness hypothesis is needed: the chosen right inverse tensors to a
right inverse. Consequently the intrinsic symmetric-algebra kernel ideal and
its exact quotient theorem can be rebuilt after every such tensor transport.

This is a genuine linear hereditary-reentry theorem. Localizations and flat
base changes are special tensor transports at the module level, but this file
does not yet identify the new intrinsic ideal with the extension of the old
ideal through a canonical symmetric-algebra base-change equivalence.
-/

namespace PCRLean
namespace Experimental
namespace SplitSurjectionTensorHeredity

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {V : Type v} {Kmod : Type w} {M : Type x}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup Kmod] [Module R Kmod]
variable [AddCommGroup M] [Module R M]

open scoped TensorProduct
open SplitSurjectionSymmetricQuotient

variable (S : SplitSurjection (R := R) (V := V) (Kmod := Kmod))

/-- Tensor the conormal projection on the right by an arbitrary module. -/
def tensorProject :
    TensorProduct R V M →ₗ[R] TensorProduct R Kmod M :=
  S.project.rTensor M

/-- Tensor the chosen right inverse by the same module. -/
def tensorLiftBack :
    TensorProduct R Kmod M →ₗ[R] TensorProduct R V M :=
  S.liftBack.rTensor M

@[simp] theorem tensorProject_tmul (v : V) (m : M) :
    S.tensorProject (v ⊗ₜ[R] m) = S.project v ⊗ₜ[R] m := by
  simp [tensorProject]

@[simp] theorem tensorLiftBack_tmul (k : Kmod) (m : M) :
    S.tensorLiftBack (k ⊗ₜ[R] m) = S.liftBack k ⊗ₜ[R] m := by
  simp [tensorLiftBack]

/-- The tensored maps still satisfy the right-inverse identity. -/
theorem tensor_rightInverse :
    S.tensorProject.comp S.tensorLiftBack = LinearMap.id := by
  rw [← LinearMap.rTensor_comp]
  rw [S.rightInverse]
  simp

/-- The split-surjection package transported through the tensor operation. -/
def tensorSplit :
    SplitSurjection
      (R := R)
      (V := TensorProduct R V M)
      (Kmod := TensorProduct R Kmod M) where
  project := S.tensorProject
  liftBack := S.tensorLiftBack
  rightInverse := S.tensor_rightInverse

@[simp] theorem tensorSplit_project :
    (S.tensorSplit (M := M)).project = S.tensorProject := rfl

@[simp] theorem tensorSplit_liftBack :
    (S.tensorSplit (M := M)).liftBack = S.tensorLiftBack := rfl

/-- Tensoring preserves surjectivity because it preserves the chosen section. -/
theorem tensorProject_surjective : Function.Surjective S.tensorProject := by
  intro y
  refine ⟨S.tensorLiftBack y, ?_⟩
  have h := congrArg
    (fun f : TensorProduct R Kmod M →ₗ[R] TensorProduct R Kmod M => f y)
    S.tensor_rightInverse
  simpa [LinearMap.comp_apply] using h

/-- A pure tensor whose first factor was in the old kernel lies in the new
kernel. -/
theorem tmul_mem_tensorKernel
    {v : V} (hv : v ∈ LinearMap.ker S.project) (m : M) :
    v ⊗ₜ[R] m ∈ LinearMap.ker S.tensorProject := by
  apply LinearMap.mem_ker.mpr
  have hv0 : S.project v = 0 := LinearMap.mem_ker.mp hv
  simp [tensorProject, hv0]

/-- The corresponding degree-one pure tensor is a generator of the transported
intrinsic actual centre ideal. -/
theorem tmul_generator_mem_tensorKernelIdeal
    {v : V} (hv : v ∈ LinearMap.ker S.project) (m : M) :
    SymmetricAlgebra.ι R (TensorProduct R V M) (v ⊗ₜ[R] m) ∈
      (S.tensorSplit (M := M)).kernelIdeal := by
  apply Ideal.subset_span
  exact ⟨⟨v ⊗ₜ[R] m, S.tmul_mem_tensorKernel hv m⟩, rfl⟩

/-- Exact quotient theorem after arbitrary tensor transport. -/
noncomputable def tensorQuotientEquiv :
    (SymmetricAlgebra R (TensorProduct R V M) ⧸
        (S.tensorSplit (M := M)).kernelIdeal) ≃+*
      SymmetricAlgebra R (TensorProduct R Kmod M) :=
  (S.tensorSplit (M := M)).quotientEquiv

/-- Whenever the transported source and target symmetric algebras satisfy the
usual Noetherian and regularity hypotheses, the tensored centre is again an
actual proper finite-type regular centre. -/
noncomputable def tensorRegularCertificate
    [Nontrivial (SymmetricAlgebra R (TensorProduct R Kmod M))]
    [IsNoetherianRing (SymmetricAlgebra R (TensorProduct R V M))]
    [IsRegularRing (SymmetricAlgebra R (TensorProduct R Kmod M))] :
    SplitSurjectionRegularCentre.Certificate (S.tensorSplit (M := M)) :=
  SplitSurjectionRegularCentre.certificate (S.tensorSplit (M := M))

end

end SplitSurjectionTensorHeredity
end Experimental
end PCRLean
