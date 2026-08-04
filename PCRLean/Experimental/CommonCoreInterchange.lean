import Mathlib

/-!
# Two-surjection common-core compiler

The X038 transport proposal does not begin with a speculative direct map
between two transformed graded objects.  Instead, both objects map
surjectively to a canonical common image-filtration core.  Their two kernels
are the Tor/base-change defect and the Valabrega/saturation defect.

If both kernels vanish, the two maps are linear equivalences and hence induce a
canonical equivalence between the left and right transformed objects.  This
file proves only that exact abstract compiler.  It does not construct the
geometric common core or identify either kernel.
-/

namespace PCRLean
namespace Experimental
namespace CommonCoreInterchange

noncomputable section

universe u v w z

variable {R : Type u} [CommRing R]
variable (Left : Type v) (Right : Type w) (Core : Type z)
variable [AddCommGroup Left] [Module R Left]
variable [AddCommGroup Right] [Module R Right]
variable [AddCommGroup Core] [Module R Core]

/-- Two transformed objects equipped with surjections to one common core. -/
structure Cospan where
  leftMap : Left →ₗ[R] Core
  rightMap : Right →ₗ[R] Core
  left_surjective : Function.Surjective leftMap
  right_surjective : Function.Surjective rightMap

namespace Cospan

variable {Left Right Core}

/-- Vanishing of the left kernel turns the left comparison into an equivalence. -/
noncomputable def leftEquiv
    (c : Cospan (R := R) Left Right Core)
    (hleft : LinearMap.ker c.leftMap = ⊥) :
    Left ≃ₗ[R] Core :=
  LinearEquiv.ofBijective c.leftMap
    ⟨LinearMap.ker_eq_bot.mp hleft, c.left_surjective⟩

/-- Vanishing of the right kernel turns the right comparison into an equivalence. -/
noncomputable def rightEquiv
    (c : Cospan (R := R) Left Right Core)
    (hright : LinearMap.ker c.rightMap = ⊥) :
    Right ≃ₗ[R] Core :=
  LinearEquiv.ofBijective c.rightMap
    ⟨LinearMap.ker_eq_bot.mp hright, c.right_surjective⟩

/-- If both defect kernels vanish, the two transformed objects are canonically
linearly equivalent through the common core. -/
noncomputable def interchangeEquiv
    (c : Cospan (R := R) Left Right Core)
    (hleft : LinearMap.ker c.leftMap = ⊥)
    (hright : LinearMap.ker c.rightMap = ⊥) :
    Left ≃ₗ[R] Right :=
  (c.leftEquiv hleft).trans (c.rightEquiv hright).symm

/-- Pointwise compatibility of the common-core equivalence with the two
surjections. -/
theorem rightMap_interchangeEquiv_apply
    (c : Cospan (R := R) Left Right Core)
    (hleft : LinearMap.ker c.leftMap = ⊥)
    (hright : LinearMap.ker c.rightMap = ⊥)
    (x : Left) :
    c.rightMap (c.interchangeEquiv hleft hright x) = c.leftMap x := by
  change (c.rightEquiv hright)
      ((c.rightEquiv hright).symm ((c.leftEquiv hleft) x)) = c.leftMap x
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Existential form used by higher-level compiler interfaces. -/
theorem nonempty_equiv_of_kernel_vanishing
    (c : Cospan (R := R) Left Right Core)
    (hleft : LinearMap.ker c.leftMap = ⊥)
    (hright : LinearMap.ker c.rightMap = ⊥) :
    Nonempty (Left ≃ₗ[R] Right) :=
  ⟨c.interchangeEquiv hleft hright⟩

end Cospan

end

end CommonCoreInterchange
end Experimental
end PCRLean
