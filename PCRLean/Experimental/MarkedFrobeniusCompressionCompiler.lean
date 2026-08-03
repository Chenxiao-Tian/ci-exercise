import Mathlib
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Marked Frobenius compression compiler

Once an actual centre ideal reflects prime-power roots, every family of rooted
marked equations may be compressed simultaneously:

`(g_i^(p^e), (p^e)m_i)` is permissible for the centre exactly when
`(g_i,m_i)` is.

The theorem is independent of coordinates and of the mechanism used to prove
Frobenius-normality.  It applies equally to coordinate, affine linear,
polynomial graph and faithfully-flat descended centres.

The dependent multi-owner version closes the active-owner component of graded
Frobenius normalization.  It deliberately does not infer passive Tor safety,
normal flatness or boundary transversality.
-/

namespace PCRLean
namespace Experimental
namespace MarkedFrobeniusCompressionCompiler

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {κ : Type v}

/-- One rooted marked equation preserves centre permissibility. -/
theorem one_owner_iff
    (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (e : Nat) (g : A) (mark : Nat) :
    g ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔
      g ∈ I ^ mark :=
  FrobeniusNormalCentre.power_mem_scaled_iff
    p I hreflect e mark g

/-- An indexed family preserves joint centre permissibility componentwise. -/
theorem family_iff
    (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (e : Nat) (root : κ → A) (mark : κ → Nat) :
    (∀ i, (root i) ^ (p ^ e) ∈ I ^ ((p ^ e) * mark i)) ↔
      (∀ i, root i ∈ I ^ mark i) := by
  constructor
  · intro h i
    exact (one_owner_iff p I hreflect e (root i) (mark i)).mp (h i)
  · intro h i
    exact (one_owner_iff p I hreflect e (root i) (mark i)).mpr (h i)

/-- Explicit source equations identified with prime powers inherit the same
joint permissibility equivalence. -/
theorem family_root_identity_iff
    (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (e : Nat) (source root : κ → A) (mark : κ → Nat)
    (hroot : ∀ i, (root i) ^ (p ^ e) = source i) :
    (∀ i, source i ∈ I ^ ((p ^ e) * mark i)) ↔
      (∀ i, root i ∈ I ^ mark i) := by
  constructor
  · intro h i
    apply (one_owner_iff p I hreflect e (root i) (mark i)).mp
    rw [hroot i]
    exact h i
  · intro h i
    rw [← hroot i]
    exact (one_owner_iff p I hreflect e (root i) (mark i)).mpr (h i)

/-- Several active-owner packets with a common Frobenius level compress
without changing joint permissibility. -/
theorem multiOwner_iff
    {Owner : Type v} {Row : Owner → Type w}
    (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (e : Nat)
    (root : (o : Owner) → Row o → A)
    (mark : (o : Owner) → Row o → Nat) :
    (∀ o i, (root o i) ^ (p ^ e) ∈
        I ^ ((p ^ e) * mark o i)) ↔
      (∀ o i, root o i ∈ I ^ mark o i) := by
  constructor
  · intro h o i
    exact (one_owner_iff p I hreflect e
      (root o i) (mark o i)).mp (h o i)
  · intro h o i
    exact (one_owner_iff p I hreflect e
      (root o i) (mark o i)).mpr (h o i)

/-- Owners may carry different Frobenius levels, provided the centre reflects
all prime-power levels. -/
theorem multiOwner_variableLevel_iff
    {Owner : Type v} {Row : Owner → Type w}
    (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (level : (o : Owner) → Row o → Nat)
    (root : (o : Owner) → Row o → A)
    (mark : (o : Owner) → Row o → Nat) :
    (∀ o i, (root o i) ^ (p ^ level o i) ∈
        I ^ ((p ^ level o i) * mark o i)) ↔
      (∀ o i, root o i ∈ I ^ mark o i) := by
  constructor
  · intro h o i
    exact (one_owner_iff p I hreflect (level o i)
      (root o i) (mark o i)).mp (h o i)
  · intro h o i
    exact (one_owner_iff p I hreflect (level o i)
      (root o i) (mark o i)).mpr (h o i)

end

end MarkedFrobeniusCompressionCompiler
end Experimental
end PCRLean
