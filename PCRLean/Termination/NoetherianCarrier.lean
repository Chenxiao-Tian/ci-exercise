import Mathlib
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherian carrier payment

A finite coupon set is not the only way to exclude infinitely many financed
births.  If every accepted event strictly enlarges one consumed submodule in a
fixed Noetherian ancestor carrier, the event relation is well founded.  Gauge,
chart, cleaning, and reentry changes are allowed only when they preserve that
same carrier and consumed submodule.

This is a genuine termination theorem.  The unresolved geometric task is to
construct the fixed carrier and prove strict enlargement for every new birth.
-/

namespace PCRLean.Termination.NoetherianCarrier

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- `PaymentStep new old` means the event has permanently consumed a strictly
larger ancestor submodule. -/
def PaymentStep (new old : Submodule R M) : Prop :=
  old < new

/-- Strict consumption in a fixed Noetherian carrier is well founded. -/
theorem paymentStep_wellFounded :
    WellFounded (PaymentStep (R := R) (M := M)) := by
  exact IsNoetherian.wf (inferInstance : IsNoetherian R M)

/-- There is no infinite path of strictly enlarging consumed submodules. -/
theorem no_infinite_payment_chain :
    IsEmpty {f : ℕ → Submodule R M //
      ∀ n, PaymentStep (f (n + 1)) (f n)} :=
  wellFounded_iff_isEmpty_descending_chain.mp paymentStep_wellFounded

/-- An exact reentry map preserves the consumed carrier state and therefore is
not itself a progress edge. -/
def PreservesConsumed (before after : Submodule R M) : Prop :=
  after = before

/-- A preserving transition cannot simultaneously be a strict payment. -/
theorem preserve_not_payment {before after : Submodule R M}
    (hpres : PreservesConsumed before after) :
    ¬ PaymentStep after before := by
  intro hpay
  rw [hpres] at hpay
  exact (lt_irrefl before) hpay

/-- Every accepted strict payment is irreversible in the order-theoretic
sense: the old consumed submodule is properly contained in the new one. -/
theorem old_lt_new_of_payment {before after : Submodule R M}
    (h : PaymentStep after before) : before < after := h

end PCRLean.Termination.NoetherianCarrier
