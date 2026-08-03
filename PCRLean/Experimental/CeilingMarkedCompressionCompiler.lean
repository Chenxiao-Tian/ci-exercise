import Mathlib
import PCRLean.Experimental.CeilingMarkedPowerReflection

/-!
# Arbitrary-mark Frobenius compression for owner packets

Under prime-power injectivity of the normal-cone layers, each owner row may be
compressed independently:

`(g_i^(p^e_i), m_i)`

is permissible for the centre exactly when

`(g_i, ceil(m_i / p^e_i))`

is permissible.  No common Frobenius level and no divisibility of the original
marks is required.

This is the owner-level compiler for maximal Frobenius normalization.  It
changes only the presentation and active marks; passive, boundary and history
data must remain literally unchanged by the surrounding geometric state
compiler.
-/

namespace PCRLean
namespace Experimental
namespace CeilingMarkedCompressionCompiler

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]

/-- One arbitrary marked prime-power equation. -/
theorem one_owner_iff
    (p : Nat) [Fact p.Prime]
    (I : Ideal A)
    (hgraded : GradedPowerReflection.FrobeniusGradedReduced p I)
    (level mark : Nat) (root : A) :
    root ^ (p ^ level) ∈ I ^ mark ↔
      root ∈ I ^ CeilingMarkedPowerReflection.ceilQuot
        (p ^ level) mark (pow_pos (Fact.out : p.Prime).pos level) := by
  exact CeilingMarkedPowerReflection.frobeniusPower_mem_iff_ceilQuot
    p I hgraded level mark root

/-- An indexed family with row-dependent levels and marks. -/
theorem family_iff
    {κ : Type v}
    (p : Nat) [Fact p.Prime]
    (I : Ideal A)
    (hgraded : GradedPowerReflection.FrobeniusGradedReduced p I)
    (level mark : κ → Nat) (root : κ → A) :
    (∀ i, (root i) ^ (p ^ level i) ∈ I ^ mark i) ↔
      (∀ i, root i ∈ I ^
        CeilingMarkedPowerReflection.ceilQuot
          (p ^ level i) (mark i)
          (pow_pos (Fact.out : p.Prime).pos (level i))) := by
  constructor
  · intro h i
    exact (one_owner_iff p I hgraded
      (level i) (mark i) (root i)).mp (h i)
  · intro h i
    exact (one_owner_iff p I hgraded
      (level i) (mark i) (root i)).mpr (h i)

/-- Source equations explicitly identified with row-dependent prime powers. -/
theorem family_root_identity_iff
    {κ : Type v}
    (p : Nat) [Fact p.Prime]
    (I : Ideal A)
    (hgraded : GradedPowerReflection.FrobeniusGradedReduced p I)
    (level mark : κ → Nat)
    (source root : κ → A)
    (hroot : ∀ i, (root i) ^ (p ^ level i) = source i) :
    (∀ i, source i ∈ I ^ mark i) ↔
      (∀ i, root i ∈ I ^
        CeilingMarkedPowerReflection.ceilQuot
          (p ^ level i) (mark i)
          (pow_pos (Fact.out : p.Prime).pos (level i))) := by
  constructor
  · intro h i
    apply (one_owner_iff p I hgraded
      (level i) (mark i) (root i)).mp
    rw [hroot i]
    exact h i
  · intro h i
    rw [← hroot i]
    exact (one_owner_iff p I hgraded
      (level i) (mark i) (root i)).mpr (h i)

/-- Dependent multi-owner packet with row-dependent levels and arbitrary
marks. -/
theorem multiOwner_iff
    {Owner : Type v} {Row : Owner → Type w}
    (p : Nat) [Fact p.Prime]
    (I : Ideal A)
    (hgraded : GradedPowerReflection.FrobeniusGradedReduced p I)
    (level mark : (o : Owner) → Row o → Nat)
    (root : (o : Owner) → Row o → A) :
    (∀ o i, (root o i) ^ (p ^ level o i) ∈ I ^ mark o i) ↔
      (∀ o i, root o i ∈ I ^
        CeilingMarkedPowerReflection.ceilQuot
          (p ^ level o i) (mark o i)
          (pow_pos (Fact.out : p.Prime).pos (level o i))) := by
  constructor
  · intro h o i
    exact (one_owner_iff p I hgraded
      (level o i) (mark o i) (root o i)).mp (h o i)
  · intro h o i
    exact (one_owner_iff p I hgraded
      (level o i) (mark o i) (root o i)).mpr (h o i)

end

end CeilingMarkedCompressionCompiler
end Experimental
end PCRLean
