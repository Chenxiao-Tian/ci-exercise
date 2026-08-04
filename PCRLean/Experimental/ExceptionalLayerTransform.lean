import Mathlib
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Exceptional-layer transforms

Let `T` be the endomorphism induced locally by multiplication by an exceptional
Cartier equation.  Consuming `q` exceptional layers replaces a module by the
image of `T^q`.  Noether's first isomorphism theorem identifies that image with
the quotient by the layers killed by `T^q`.

For a coherent sheaf, a bounded exceptional-torsion exponent should identify a
finite power of this layer transform with the exceptional saturation (ordinary
strict transform), up to an invertible line-bundle twist.  The scheme-level
existence of that exponent and the comparison with an actual ambient blowup are
separate X037 obligations.  This file proves only the exact linear-algebra
compiler once the exceptional endomorphism is supplied.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalLayerTransform

noncomputable section

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `q`-layer exceptional endomorphism. -/
def layerMap (T : Module.End R M) (q : ℕ) : Module.End R M :=
  T ^ q

/-- Consuming `q` exceptional layers is canonically the quotient by the kernel
of the `q`th power. -/
noncomputable def layerQuotientEquivRange
    (T : Module.End R M) (q : ℕ) :
    (M ⧸ LinearMap.ker (layerMap T q)) ≃ₗ[R]
      LinearMap.range (layerMap T q) :=
  (layerMap T q).quotKerEquivRange

@[simp] theorem layerQuotientEquivRange_apply_mk
    (T : Module.End R M) (q : ℕ) (x : M) :
    ((layerQuotientEquivRange T q)
      (Submodule.Quotient.mk x) : M) = layerMap T q x := by
  rfl

/-- A supplied exceptional-saturation certificate.  Geometrically `torsion`
is the exceptional-power torsion and `cutoff` is a global nilpotence bound. -/
structure SaturationCertificate (T : Module.End R M) where
  torsion : Submodule R M
  cutoff : ℕ
  kernel_eq : LinearMap.ker (layerMap T cutoff) = torsion

/-- At the certified cutoff, the saturated quotient is represented by an
actual finite exceptional-layer image. -/
noncomputable def SaturationCertificate.targetEquivRange
    {T : Module.End R M}
    (c : SaturationCertificate T) :
    (M ⧸ c.torsion) ≃ₗ[R]
      LinearMap.range (layerMap T c.cutoff) := by
  rw [← c.kernel_eq]
  exact layerQuotientEquivRange T c.cutoff

/-- The target equivalence sends the class of an element to its certified
exceptional-layer transform. -/
@[simp] theorem SaturationCertificate.targetEquivRange_apply_mk
    {T : Module.End R M}
    (c : SaturationCertificate T) (x : M) :
    ((c.targetEquivRange (Submodule.Quotient.mk x)) : M) =
      layerMap T c.cutoff x := by
  subst c.torsion
  rfl

end

end ExceptionalLayerTransform
end Experimental
end PCRLean
