import Mathlib
import PCRLean.Experimental.GradedPowerReflection
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Arbitrary-mark power reflection by ceiling division

Exact reflection at scaled marks is not the end of the story. If a marked
equation has the form `g^q` but its mark `m` is not divisible by `q`, the
correct rooted mark is

`ceil(m / q) = min { n | m ≤ q*n }`.

Under the one-layer associated-graded injectivity condition, the exact law is

`g^q ∈ I^m ↔ g ∈ I^(ceil(m/q))`.

The proof avoids a fragile arithmetic implementation of ceiling division. It
defines the ceiling as the least natural number satisfying `m ≤ q*n` and then
builds membership one filtration layer at a time. Minimality guarantees that
before the final layer one has `q*r + 1 ≤ m`, allowing the graded injectivity
hypothesis to advance from `I^r` to `I^(r+1)`.

For `q = p^e` this gives the general Frobenius normalization rule

`(g^(p^e), m) ↔ (g, ceil(m/p^e))`

for every mark, not only marks divisible by `p^e`.
-/

namespace PCRLean
namespace Experimental
namespace CeilingMarkedPowerReflection

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- Existence of an admissible ceiling quotient for positive `q`. -/
theorem ceilQuot_exists (q mark : Nat) (hq : 0 < q) :
    ∃ n : Nat, mark ≤ q * n := by
  refine ⟨mark, ?_⟩
  have hqone : 1 ≤ q := hq
  simpa using Nat.mul_le_mul_right mark hqone

/-- Least `n` such that `mark ≤ q*n`, for positive `q`. -/
noncomputable def ceilQuot (q mark : Nat) (hq : 0 < q) : Nat :=
  Nat.find (ceilQuot_exists q mark hq)

/-- The defining upper inequality. -/
theorem le_mul_ceilQuot
    (q mark : Nat) (hq : 0 < q) :
    mark ≤ q * ceilQuot q mark hq :=
  Nat.find_spec (ceilQuot_exists q mark hq)

/-- Minimality of the ceiling quotient. -/
theorem not_le_mul_of_lt_ceilQuot
    (q mark : Nat) (hq : 0 < q)
    {r : Nat} (hr : r < ceilQuot q mark hq) :
    ¬ mark ≤ q * r :=
  Nat.find_min (ceilQuot_exists q mark hq) hr

/-- Adjunction: the ceiling quotient is at most every admissible quotient. -/
theorem ceilQuot_le
    (q mark : Nat) (hq : 0 < q)
    {n : Nat} (hn : mark ≤ q * n) :
    ceilQuot q mark hq ≤ n :=
  Nat.find_min' (ceilQuot_exists q mark hq) hn

/-- Every filtration level below the ceiling is forced successively. -/
theorem mem_pow_of_power_mem_arbitrary_mark
    (q mark : Nat) (hq : 0 < q)
    (I : Ideal A)
    (hgraded : GradedPowerReflection.GradedPowerInjective q I)
    {x : A} (hxpow : x ^ q ∈ I ^ mark) :
    x ∈ I ^ ceilQuot q mark hq := by
  let n := ceilQuot q mark hq
  have hlevels : ∀ r : Nat, r ≤ n → x ∈ I ^ r := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        have hrle : r ≤ n := Nat.le_trans (Nat.le_succ r) hr
        have hxr : x ∈ I ^ r := ih hrle
        have hrlt : r < n := Nat.lt_of_succ_le hr
        have hnot : ¬ mark ≤ q * r := by
          dsimp [n] at hrlt
          exact not_le_mul_of_lt_ceilQuot q mark hq hrlt
        have hstep : q * r + 1 ≤ mark := by omega
        have hxpowStep : x ^ q ∈ I ^ (q * r + 1) :=
          GradedPowerReflection.pow_le_pow_of_le I hstep hxpow
        exact hgraded r x hxr hxpowStep
  exact hlevels n le_rfl

/-- Main arbitrary-mark reflection theorem. -/
theorem power_mem_iff_ceilQuot
    (q mark : Nat) (hq : 0 < q)
    (I : Ideal A)
    (hgraded : GradedPowerReflection.GradedPowerInjective q I)
    (x : A) :
    x ^ q ∈ I ^ mark ↔
      x ∈ I ^ ceilQuot q mark hq := by
  constructor
  · exact mem_pow_of_power_mem_arbitrary_mark
      q mark hq I hgraded
  · intro hx
    have hxpow : x ^ q ∈ I ^ (q * ceilQuot q mark hq) :=
      FrobeniusNormalCentre.power_mem_scaled_of_mem
        I q (ceilQuot q mark hq) hx
    exact GradedPowerReflection.pow_le_pow_of_le I
      (le_mul_ceilQuot q mark hq) hxpow

/-- When the mark is already a multiple of `q`, ceiling compression recovers
that exact mark. -/
theorem ceilQuot_mul
    (q mark : Nat) (hq : 0 < q) :
    ceilQuot q (q * mark) hq = mark := by
  apply Nat.le_antisymm
  · exact ceilQuot_le q (q * mark) hq le_rfl
  · exact Nat.le_of_mul_le_mul_left
      (le_mul_ceilQuot q (q * mark) hq) hq

/-- Prime-power arbitrary-mark compression. -/
theorem frobeniusPower_mem_iff_ceilQuot
    (p : Nat) [Fact p.Prime]
    (I : Ideal A)
    (hgraded : GradedPowerReflection.FrobeniusGradedReduced p I)
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ mark ↔
      x ∈ I ^ ceilQuot (p ^ e) mark
        (pow_pos (Fact.out : p.Prime).pos e) := by
  exact power_mem_iff_ceilQuot
    (p ^ e) mark (pow_pos (Fact.out : p.Prime).pos e)
    I (hgraded e) x

end

end CeilingMarkedPowerReflection
end Experimental
end PCRLean
