import Mathlib
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Graded-layer criterion for Frobenius-normal centre filtrations

Let `I` be an ideal and `q > 0`.  The associated-graded obstruction to root
reflection is concentrated in one layer.  Define `GradedPowerInjective q I` by
requiring that whenever

`x ∈ I^r` and `x^q ∈ I^(q*r + 1)`, then `x ∈ I^(r+1)`.

Equivalently, a nonzero initial form in degree `r` cannot acquire zero `q`-th
power in the associated graded ring.  This is the exact property implied by
reducedness of the associated graded ring.

An induction on the mark proves that this one-layer condition implies the full
reflection theorem

`x^q ∈ I^(q*m) → x ∈ I^m`.

Thus a future scheme-level proof does not need to manipulate every mark at
once: it may prove reducedness (or just prime-power injectivity) of the normal
cone one graded layer at a time.
-/

namespace PCRLean
namespace Experimental
namespace GradedPowerReflection

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- The `q`-th power cannot kill a nonzero initial form in one associated-
graded layer. -/
def GradedPowerInjective (q : Nat) (I : Ideal A) : Prop :=
  ∀ (r : Nat) (x : A),
    x ∈ I ^ r →
      x ^ q ∈ I ^ (q * r + 1) →
        x ∈ I ^ (r + 1)

/-- Powers of an ideal form a decreasing filtration. -/
theorem pow_le_pow_of_le
    (I : Ideal A) {m n : Nat} (hmn : m ≤ n) :
    I ^ n ≤ I ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  calc
    I ^ m * I ^ k ≤ I ^ m * ⊤ := mul_le_mul_left' le_top _
    _ = I ^ m := by simp

/-- A one-layer injectivity certificate implies reflection at every mark. -/
theorem reflects_power_of_gradedPowerInjective
    (q : Nat) (hq : 0 < q) (I : Ideal A)
    (hgraded : GradedPowerInjective q I) :
    ∀ (mark : Nat) (x : A),
      x ^ q ∈ I ^ (q * mark) → x ∈ I ^ mark := by
  intro mark
  induction mark with
  | zero =>
      intro x hx
      simp
  | succ mark ih =>
      intro x hx
      have hcoarseExp : q * mark ≤ q * (mark + 1) := by
        exact Nat.mul_le_mul_left q (Nat.le_succ mark)
      have hcoarse : x ^ q ∈ I ^ (q * mark) :=
        pow_le_pow_of_le I hcoarseExp hx
      have hxmark : x ∈ I ^ mark := ih x hcoarse
      have hlayerExp : q * mark + 1 ≤ q * (mark + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hlayer : x ^ q ∈ I ^ (q * mark + 1) :=
        pow_le_pow_of_le I hlayerExp hx
      exact hgraded mark x hxmark hlayer

/-- Exact power-membership equivalence under the graded-layer condition. -/
theorem power_mem_scaled_iff_of_gradedPowerInjective
    (q : Nat) (hq : 0 < q) (I : Ideal A)
    (hgraded : GradedPowerInjective q I)
    (mark : Nat) (x : A) :
    x ^ q ∈ I ^ (q * mark) ↔ x ∈ I ^ mark := by
  constructor
  · exact reflects_power_of_gradedPowerInjective q hq I hgraded mark x
  · exact FrobeniusNormalCentre.power_mem_scaled_of_mem I q mark

/-- Prime-power injectivity in every graded layer. -/
def FrobeniusGradedReduced (p : Nat) (I : Ideal A) : Prop :=
  ∀ e : Nat, GradedPowerInjective (p ^ e) I

/-- Graded prime-power injectivity implies a Frobenius-normal centre
filtration. -/
theorem reflectsFrobeniusPowers_of_frobeniusGradedReduced
    (p : Nat) [Fact p.Prime] (I : Ideal A)
    (hgraded : FrobeniusGradedReduced p I) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  intro e mark x hx
  exact reflects_power_of_gradedPowerInjective
    (p ^ e) (pow_pos (Fact.out : p.Prime).pos e) I
    (hgraded e) mark x hx

/-- Exact scaled marked heredity follows from graded prime-power injectivity. -/
theorem frobeniusPower_mem_scaled_iff_of_frobeniusGradedReduced
    (p : Nat) [Fact p.Prime] (I : Ideal A)
    (hgraded : FrobeniusGradedReduced p I)
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔
      x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflectsFrobeniusPowers_of_frobeniusGradedReduced p I hgraded)
    e mark x

end

end GradedPowerReflection
end Experimental
end PCRLean
