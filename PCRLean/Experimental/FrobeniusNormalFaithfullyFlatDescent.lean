import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Faithfully flat descent of Frobenius-normal centre filtrations

Let `A → B` be faithfully flat and let `I` be an ideal of `A`.  If the extended
ideal `I B` reflects all prime-power roots in its power filtration, then `I`
reflects them in `A`.

The proof is short but structurally decisive:

1. extend a membership `x^(p^e) ∈ I^((p^e)m)` to `B`;
2. apply Frobenius reflection for `I B`;
3. contract the resulting membership back to `A`;
4. use faithful-flat descent `(I^m B) ∩ A = I^m`.

This is the local-to-global mechanism needed to transport the coordinate-centre
theorems through an étale or faithfully flat coordinate cover.  The remaining
geometric theorem is to produce such a cover for every regular centre and to
identify the pulled-back ideal with a coordinate ideal.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalFaithfullyFlatDescent

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Extension of a centre ideal. -/
def extendedIdeal (I : Ideal A) : Ideal B :=
  Ideal.map (algebraMap A B) I

/-- Faithful flatness reflects membership in every extended ideal. -/
theorem mem_iff_map_mem_extended
    (I : Ideal A) (x : A) :
    x ∈ I ↔ algebraMap A B x ∈ extendedIdeal (B := B) I := by
  change x ∈ I ↔ x ∈
    (extendedIdeal (B := B) I).comap (algebraMap A B)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- Extension commutes with ideal powers. -/
theorem extendedIdeal_pow
    (I : Ideal A) (n : Nat) :
    extendedIdeal (B := B) (I ^ n) =
      (extendedIdeal (B := B) I) ^ n := by
  exact Ideal.map_pow (algebraMap A B) I n

/-- Frobenius-normality descends along a faithfully flat algebra. -/
theorem reflectsFrobeniusPowers_of_extended
    (p : Nat) (I : Ideal A)
    (hB : FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (extendedIdeal (B := B) I)) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  intro e mark x hx
  have hxmap :
      algebraMap A B (x ^ (p ^ e)) ∈
        extendedIdeal (B := B) (I ^ ((p ^ e) * mark)) :=
    Ideal.mem_map_of_mem (algebraMap A B) hx
  have hxmap' :
      (algebraMap A B x) ^ (p ^ e) ∈
        (extendedIdeal (B := B) I) ^ ((p ^ e) * mark) := by
    rw [map_pow] at hxmap
    rw [extendedIdeal_pow] at hxmap
    exact hxmap
  have hrootB :
      algebraMap A B x ∈
        (extendedIdeal (B := B) I) ^ mark :=
    hB e mark (algebraMap A B x) hxmap'
  have hrootB' :
      algebraMap A B x ∈
        extendedIdeal (B := B) (I ^ mark) := by
    rw [extendedIdeal_pow]
    exact hrootB
  exact (mem_iff_map_mem_extended (B := B) (I ^ mark) x).mpr hrootB'

/-- Exact scaled marked heredity descends from the extended ideal. -/
theorem power_mem_scaled_iff_of_extended
    (p : Nat) (I : Ideal A)
    (hB : FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (extendedIdeal (B := B) I))
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔
      x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflectsFrobeniusPowers_of_extended (B := B) p I hB)
    e mark x

end

end FrobeniusNormalFaithfullyFlatDescent
end Experimental
end PCRLean
