import Mathlib
import PCRLean.Experimental.CeilingMarkedPowerReflection
import PCRLean.Experimental.ControlledFrobeniusTransform

/-!
# Exceptional debt under arbitrary-mark Frobenius compression

For a power equation `f = g^q` with arbitrary mark `m`, the rooted mark is

`n = ceil(m/q)`.

The discrepancy

`δ = q*n - m`

satisfies `0 ≤ δ < q`.  If on a blowup chart

`φ(g) = E^n * g'`,

then the source controlled transform at mark `m` is not simply `(g')^q` unless
`q ∣ m`.  The exact factorization is

`φ(g^q) = E^m * (E^δ * (g')^q)`.

Thus arbitrary-mark compression preserves the active singular condition but
creates a bounded exceptional monomial debt.  The debt must be enrolled in the
boundary/history ledger; silently dropping it would break hereditary reentry.
For marks divisible by `q`, `δ = 0` and the earlier exact transform identity is
recovered.
-/

namespace PCRLean
namespace Experimental
namespace CeilingControlledTransformDebt

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

/-- Bounded exceptional discrepancy between the scaled rooted mark and the
original mark. -/
def deficit (q mark : Nat) (hq : 0 < q) : Nat :=
  q * CeilingMarkedPowerReflection.ceilQuot q mark hq - mark

/-- Original mark plus debt equals the fully scaled rooted mark. -/
theorem mark_add_deficit
    (q mark : Nat) (hq : 0 < q) :
    mark + deficit q mark hq =
      q * CeilingMarkedPowerReflection.ceilQuot q mark hq := by
  unfold deficit
  exact Nat.add_sub_of_le
    (CeilingMarkedPowerReflection.le_mul_ceilQuot q mark hq)

/-- The debt is always strictly smaller than one root block. -/
theorem deficit_lt
    (q mark : Nat) (hq : 0 < q) :
    deficit q mark hq < q := by
  let n := CeilingMarkedPowerReflection.ceilQuot q mark hq
  have hupper : mark ≤ q * n := by
    dsimp [n]
    exact CeilingMarkedPowerReflection.le_mul_ceilQuot q mark hq
  cases hn : n with
  | zero =>
      have hmark : mark = 0 := by omega
      simp [deficit, n, hn, hmark, hq]
  | succ r =>
      have hrlt : r < CeilingMarkedPowerReflection.ceilQuot q mark hq := by
        rw [← show n = CeilingMarkedPowerReflection.ceilQuot q mark hq from rfl,
          hn]
        exact Nat.lt_succ_self r
      have hnot : ¬ mark ≤ q * r :=
        CeilingMarkedPowerReflection.not_le_mul_of_lt_ceilQuot
          q mark hq hrlt
      unfold deficit
      dsimp [n] at hupper
      rw [hn] at hupper ⊢
      omega

/-- The debt vanishes for exactly scaled marks. -/
theorem deficit_mul
    (q mark : Nat) (hq : 0 < q) :
    deficit q (q * mark) hq = 0 := by
  rw [deficit, CeilingMarkedPowerReflection.ceilQuot_mul q mark hq]
  simp

/-- Exact controlled factorization with bounded exceptional debt. -/
theorem root_factorization_with_debt
    (φ : A →+* B) (root : A) (E root' : B)
    (q mark : Nat) (hq : 0 < q)
    (hfactor : φ root =
      E ^ CeilingMarkedPowerReflection.ceilQuot q mark hq * root') :
    φ (root ^ q) =
      E ^ mark *
        (E ^ deficit q mark hq * root' ^ q) := by
  calc
    φ (root ^ q) =
        E ^ (q * CeilingMarkedPowerReflection.ceilQuot q mark hq) *
          root' ^ q :=
      ControlledFrobeniusTransform.root_factorization
        φ root E root' q
        (CeilingMarkedPowerReflection.ceilQuot q mark hq) hfactor
    _ = E ^ (mark + deficit q mark hq) * root' ^ q := by
      rw [mark_add_deficit]
    _ = E ^ mark * (E ^ deficit q mark hq * root' ^ q) := by
      rw [pow_add]
      ac_rfl

/-- Explicit source-equation version. -/
theorem source_factorization_with_debt
    (φ : A →+* B) (source root : A) (E root' : B)
    (q mark : Nat) (hq : 0 < q)
    (hsource : root ^ q = source)
    (hfactor : φ root =
      E ^ CeilingMarkedPowerReflection.ceilQuot q mark hq * root') :
    φ source =
      E ^ mark *
        (E ^ deficit q mark hq * root' ^ q) := by
  rw [← hsource]
  exact root_factorization_with_debt
    φ root E root' q mark hq hfactor

/-- At a divisible mark the debt formula reduces to the exact power of the root
controlled transform. -/
theorem root_factorization_scaled_mark
    (φ : A →+* B) (root : A) (E root' : B)
    (q mark : Nat) (hq : 0 < q)
    (hfactor : φ root = E ^ mark * root') :
    φ (root ^ q) = E ^ (q * mark) * root' ^ q := by
  exact ControlledFrobeniusTransform.root_factorization
    φ root E root' q mark hfactor

end

end CeilingControlledTransformDebt
end Experimental
end PCRLean
