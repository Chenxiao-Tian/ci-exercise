import Mathlib
import PCRLean.Experimental.DivisorWordSaturation

/-!
# Finite saturated source capsules

A source word carries more than its final modification morphism.  After all
exceptional components have been recorded, however, its degree-zero saturated
transform is determined by

* the finite divisor word;
* the inherited submodule to be removed; and
* a finite exponent certifying stabilization of power torsion.

This file packages that finite data and proves that the resulting submodule and
quotient are invariant under permutation of the divisor word.  The scheme-level
X041 bridge must construct such a capsule from a centre-enriched blowup word and
identify its quotient with the actual iterated strict transform.
-/

namespace PCRLean
namespace Experimental
namespace SaturatedSourceCapsule

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open PowerSaturationProduct DivisorWordSaturation

/-- A finite certificate that one exponent detects the full power saturation. -/
structure ExponentCertificate (q : R) (N : Submodule R M) (e : ℕ) : Prop where
  complete : ∀ x : M,
    x ∈ powerSaturation q N ↔ q ^ e • x ∈ N

namespace ExponentCertificate

/-- Every larger exponent is also a complete certificate. -/
theorem mono
    {q : R} {N : Submodule R M} {e f : ℕ}
    (c : ExponentCertificate q N e)
    (hef : e ≤ f) :
    ExponentCertificate q N f := by
  refine ⟨?_⟩
  intro x
  constructor
  · intro hx
    have he : q ^ e • x ∈ N := (c.complete x).mp hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hef
    simpa [pow_add, smul_smul, mul_comm] using N.smul_mem (q ^ d) he
  · intro hx
    exact ⟨f, hx⟩

end ExponentCertificate

/-- A finite degree-zero source-transform capsule. -/
structure Capsule where
  divisorWord : List R
  inherited : Submodule R M
  exponent : ℕ
  exponentCertificate :
    ExponentCertificate divisorWord.prod inherited exponent

namespace Capsule

variable (C : Capsule (R := R) (M := M))

/-- The full exceptional-power saturation carried by the capsule. -/
def saturatedSubmodule : Submodule R M :=
  powerSaturation C.divisorWord.prod C.inherited

/-- The degree-zero saturated source transform. -/
abbrev Transform := M ⧸ C.saturatedSubmodule

/-- The recorded exponent computes the full saturated submodule. -/
theorem mem_saturatedSubmodule_iff (x : M) :
    x ∈ C.saturatedSubmodule ↔
      C.divisorWord.prod ^ C.exponent • x ∈ C.inherited :=
  C.exponentCertificate.complete x

/-- Successive saturation along the word gives exactly the capsule submodule. -/
theorem wordSaturation_eq :
    wordSaturation C.divisorWord C.inherited = C.saturatedSubmodule := by
  exact wordSaturation_eq_prod C.divisorWord C.inherited

/-- Reordering the exceptional components leaves the saturated submodule
unchanged. -/
theorem saturatedSubmodule_eq_of_perm
    (D : Capsule (R := R) (M := M))
    (hword : C.divisorWord.Perm D.divisorWord)
    (hinherited : C.inherited = D.inherited) :
    C.saturatedSubmodule = D.saturatedSubmodule := by
  unfold saturatedSubmodule
  rw [hinherited, hword.prod_eq]

/-- Therefore the two degree-zero source transforms are canonically linearly
equivalent. -/
noncomputable def transformEquivOfPerm
    (D : Capsule (R := R) (M := M))
    (hword : C.divisorWord.Perm D.divisorWord)
    (hinherited : C.inherited = D.inherited) :
    C.Transform ≃ₗ[R] D.Transform := by
  have hsub := C.saturatedSubmodule_eq_of_perm D hword hinherited
  rw [hsub]
  exact LinearEquiv.refl R _

end Capsule

end

end SaturatedSourceCapsule
end Experimental
end PCRLean
