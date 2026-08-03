import Mathlib
import PCRLean.Experimental.UnivariateFrobeniusOrderHeredity

/-!
# Frobenius mark-scaling boundary

Integral equivalence of two weighted presentations is not enough by itself:
the grading must be compressed together with the Frobenius root.  The example
`X^q` versus `X` shows that retaining the old mark changes the singular
condition whenever `q > 1`.

The same file promotes the one-equation order-heredity theorem to an arbitrary
indexed family, and hence to equality of the pointwise marked singular sets of
a finite principal presentation after simultaneous Frobenius compression.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusMarkScalingBoundary

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {κ : Type v}

open UnivariateFrobeniusOrderHeredity

/-- The powered coordinate has order exactly `q`, so it is singular at mark
`q`. -/
theorem X_pow_singular_at_scaled_mark
    (q : Nat) (hq : 0 < q) :
    AtOriginSingular ((Polynomial.X : K[X]) ^ q) q := by
  right
  rw [natTrailingDegree_pow (Polynomial.X : K[X]) q Polynomial.X_ne_zero]
  simp

/-- The root coordinate itself is not singular at the old mark when `q > 1`. -/
theorem X_not_singular_at_unscaled_mark
    (q : Nat) (hq : 1 < q) :
    ¬ AtOriginSingular (Polynomial.X : K[X]) q := by
  simp [AtOriginSingular, hq.not_le]

/-- Minimal counterexample: replacing `X^q` by `X` without dividing the mark
changes the marked singular condition. -/
theorem unscaled_mark_counterexample
    (q : Nat) (hq : 1 < q) :
    AtOriginSingular ((Polynomial.X : K[X]) ^ q) q ∧
      ¬ AtOriginSingular (Polynomial.X : K[X]) q := by
  exact ⟨X_pow_singular_at_scaled_mark q (lt_trans Nat.zero_lt_one hq),
    X_not_singular_at_unscaled_mark q hq⟩

/-- Simultaneous Frobenius compression preserves the marked singular condition
for every equation in an indexed family. -/
theorem family_pow_iff
    (q : Nat) (hq : 0 < q)
    (a : K) (root : κ → K[X]) (mark : κ → Nat) :
    (∀ j, AtPointSingular a ((root j) ^ q) (q * mark j)) ↔
      (∀ j, AtPointSingular a (root j) (mark j)) := by
  constructor
  · intro h j
    exact (atPointSingular_pow_iff q (mark j) hq a (root j)).mp (h j)
  · intro h j
    exact (atPointSingular_pow_iff q (mark j) hq a (root j)).mpr (h j)

/-- Pointwise singular set of a weighted principal family. -/
def singularSet
    (equation : κ → K[X]) (mark : κ → Nat) : Set K :=
  {a | ∀ j, AtPointSingular a (equation j) (mark j)}

/-- The singular sets of a family of powers and its mark-compressed root family
are equal. -/
theorem singularSet_pow_eq
    (q : Nat) (hq : 0 < q)
    (root : κ → K[X]) (mark : κ → Nat) :
    singularSet (fun j => (root j) ^ q) (fun j => q * mark j) =
      singularSet root mark := by
  ext a
  exact family_pow_iff q hq a root mark

section Perfect

variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- A finite or indexed derivative-zero family has the same pointwise marked
singular set as its canonical perfect-field root family with divided marks. -/
theorem derivativeZero_family_singularSet_eq
    (equation : κ → K[X]) (mark : κ → Nat)
    (hderiv : ∀ j, Polynomial.derivative (equation j) = 0) :
    singularSet equation (fun j => p * mark j) =
      singularSet
        (fun j => PolynomialFrobeniusExtraction.frobeniusRoot p (equation j))
        mark := by
  ext a
  constructor
  · intro h j
    exact (derivativeZero_root_preserves_atPoint p (mark j) a
      (equation j) (hderiv j)).mp (h j)
  · intro h j
    exact (derivativeZero_root_preserves_atPoint p (mark j) a
      (equation j) (hderiv j)).mpr (h j)

end Perfect

end

end FrobeniusMarkScalingBoundary
end Experimental
end PCRLean
