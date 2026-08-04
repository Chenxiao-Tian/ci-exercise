import Mathlib

/-!
# Weighted contact cleaning

The scalar chart model for an ambientized flatifier is

`u^q * a - u^m * b`.

Here `u = 0` is the exceptional divisor, `q > 0` is the exceptional charge of
the normal equation, and `m` is the current contact/saturation debt.  If
`q ≤ m`, division by the common exceptional factor `u^q` leaves debt `m-q`.
If `m ≤ q`, division by `u^m` produces a residual expression with no positive
constant contact debt; in the graph model with `b = 1`, the carrier chart is
terminal.

The scheme-level assertion that every projective-normal discrepancy admits such
an adapted finite presentation is a separate bi-Rees transport obligation.
-/

namespace PCRLean
namespace Experimental
namespace WeightedContactCleaning

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The continuing chart factorization when the exceptional charge does not
exceed the current debt. -/
theorem factor_continuing
    (u a b : R) {q m : ℕ} (hqm : q ≤ m) :
    u ^ q * a - u ^ m * b =
      u ^ q * (a - u ^ (m - q) * b) := by
  have hpow : u ^ m = u ^ q * u ^ (m - q) := by
    rw [← Nat.add_sub_of_le hqm, pow_add]
  rw [hpow]
  ring

/-- The terminal-side factorization when the current debt is no larger than the
exceptional charge. -/
theorem factor_terminal
    (u a b : R) {q m : ℕ} (hmq : m ≤ q) :
    u ^ q * a - u ^ m * b =
      u ^ m * (u ^ (q - m) * a - b) := by
  have hpow : u ^ q = u ^ m * u ^ (q - m) := by
    rw [← Nat.add_sub_of_le hmq, pow_add]
  rw [hpow]
  ring

/-- A positive weighted cleaning charge strictly lowers a debt that it does not
exceed. -/
theorem debt_drop
    {q m : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    m - q < m := by
  omega

/-- One weighted exceptional cleaning step. -/
structure Step (oldDebt newDebt charge : ℕ) : Prop where
  positiveCharge : 0 < charge
  charge_le : charge ≤ oldDebt
  residual_eq : newDebt = oldDebt - charge

/-- Every weighted cleaning step is strict. -/
theorem Step.strict
    {oldDebt newDebt charge : ℕ}
    (h : Step oldDebt newDebt charge) :
    newDebt < oldDebt := by
  rw [h.residual_eq]
  exact debt_drop h.positiveCharge h.charge_le

/-- Charges compose numerically whenever their sum remains within the original
debt. -/
theorem two_stage_residual
    {m q r : ℕ} (hqr : q + r ≤ m) :
    (m - q) - r = m - (q + r) := by
  omega

end

end WeightedContactCleaning
end Experimental
end PCRLean
