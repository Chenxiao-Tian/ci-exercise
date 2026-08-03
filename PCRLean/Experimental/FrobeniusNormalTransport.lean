import Mathlib
import PCRLean.Experimental.FrobeniusNormalCentre
import PCRLean.Experimental.GradedPowerReflection

/-!
# Transport of Frobenius-normal filtrations through ring equivalences

The ideal-adic root-reflection property is intrinsic.  If a ring equivalence
carries `I ⊂ A` to `J ⊂ B`, then exact membership in all ideal powers is
transported by the inverse equivalence.  Consequently Frobenius-normality and
the one-layer graded criterion transport without repeating a coordinate order
calculation.

This separates two tasks:

* geometry constructs an actual frame, graph presentation or overlap
  equivalence; and
* the present algebraic theorem transports the already proved filtration
  certificate.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalTransport

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

/-- Membership in a mapped ideal power is detected after applying the inverse
ring equivalence. -/
theorem mem_map_pow_iff
    (e : A ≃+* B) (I : Ideal A) (n : Nat) (y : B) :
    y ∈ (Ideal.map e I) ^ n ↔ e.symm y ∈ I ^ n := by
  rw [← Ideal.map_pow]
  simpa using
    (Ideal.apply_mem_of_equiv_iff
      (f := e) (I := I ^ n) (x := e.symm y))

/-- Frobenius-normality is invariant under a ring equivalence. -/
theorem reflectsFrobeniusPowers_map_equiv
    (e : A ≃+* B) (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p (Ideal.map e I) := by
  intro level mark y hy
  have hy' :
      (e.symm y) ^ (p ^ level) ∈ I ^ ((p ^ level) * mark) := by
    have h := (mem_map_pow_iff e I ((p ^ level) * mark)
      (y ^ (p ^ level))).mp hy
    simpa using h
  have hroot := hreflect level mark (e.symm y) hy'
  exact (mem_map_pow_iff e I mark y).mpr hroot

/-- Exact marked heredity transports through an equivalence. -/
theorem power_mem_scaled_iff_map_equiv
    (e : A ≃+* B) (p : Nat) (I : Ideal A)
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p I)
    (level mark : Nat) (y : B) :
    y ^ (p ^ level) ∈ (Ideal.map e I) ^ ((p ^ level) * mark) ↔
      y ∈ (Ideal.map e I) ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p (Ideal.map e I)
    (reflectsFrobeniusPowers_map_equiv e p I hreflect)
    level mark y

/-- The one-layer associated-graded criterion transports through a ring
equivalence. -/
theorem gradedPowerInjective_map_equiv
    (e : A ≃+* B) (q : Nat) (I : Ideal A)
    (hgraded : GradedPowerReflection.GradedPowerInjective q I) :
    GradedPowerReflection.GradedPowerInjective q (Ideal.map e I) := by
  intro r y hyr hynext
  have hyr' : e.symm y ∈ I ^ r :=
    (mem_map_pow_iff e I r y).mp hyr
  have hynext' : (e.symm y) ^ q ∈ I ^ (q * r + 1) := by
    have h := (mem_map_pow_iff e I (q * r + 1) (y ^ q)).mp hynext
    simpa using h
  have hroot := hgraded r (e.symm y) hyr' hynext'
  exact (mem_map_pow_iff e I (r + 1) y).mpr hroot

end

end FrobeniusNormalTransport
end Experimental
end PCRLean
