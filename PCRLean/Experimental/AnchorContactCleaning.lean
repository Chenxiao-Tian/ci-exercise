import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Anchor-contact cleaning

In an anchor graph chart, suppose a transverse graph difference has the form

`f = u^e * g`

where `u = 0` is the exceptional divisor.  Blowing up a regular centre carried
by the anchor divides every graph difference by one exceptional factor.  Thus
the residual contact is `u^(e-1) * g` whenever `e > 0`.

The numerical contact coordinate must precede exceptional debt in the global
rank: the contact order then decreases even if the cleaning step creates or
relabels debt.  The file proves this exact local algebra and rank arithmetic.
It does not prove that an arbitrary scheme-theoretic intersection admits the
required anchor chart, nor that the same centre is passive- and SNC-safe.
-/

namespace PCRLean
namespace Experimental
namespace AnchorContactCleaning

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Removing one exceptional factor from a positive contact monomial. -/
theorem factor_one_exceptional
    (u g : R) {e : ℕ} (he : 0 < e) :
    u ^ e * g = u * (u ^ (e - 1) * g) := by
  have hOne : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt he)
  have hExp : e - 1 + 1 = e := Nat.sub_add_cancel hOne
  calc
    u ^ e * g = u ^ (e - 1 + 1) * g := by rw [hExp]
    _ = (u ^ (e - 1) * u) * g := by rw [pow_succ]
    _ = u * (u ^ (e - 1) * g) := by ac_rfl

/-- One scalar cleaning step. -/
structure CleaningStep (oldOrder newOrder : ℕ) : Prop where
  positive : 0 < oldOrder
  residual_eq : newOrder = oldOrder - 1

/-- Every scalar cleaning step strictly lowers contact order. -/
theorem CleaningStep.contactDrop
    {oldOrder newOrder : ℕ}
    (h : CleaningStep oldOrder newOrder) :
    newOrder < oldOrder := by
  rw [h.residual_eq]
  exact Nat.sub_lt h.positive Nat.zero_lt_one

/-- Contact order followed by exceptional debt. -/
abbrev ContactDebtRank := ℕ ×ₗ ℕ

/-- Build the contact/debt rank. -/
def rank (contact debt : ℕ) : ContactDebtRank :=
  toLex (contact, debt)

/-- A strict contact drop dominates every possible change in debt. -/
theorem rank_drop_of_contact
    {oldContact newContact oldDebt newDebt : ℕ}
    (hContact : newContact < oldContact) :
    rank newContact newDebt < rank oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hContact)

/-- A cleaning step is strict in the global contact/debt rank even when the
successor debt coordinate is arbitrary. -/
theorem CleaningStep.rankDrop
    {oldContact newContact oldDebt newDebt : ℕ}
    (h : CleaningStep oldContact newContact) :
    rank newContact newDebt < rank oldContact oldDebt :=
  rank_drop_of_contact h.contactDrop

/-- At fixed contact order, ordinary debt cleanup remains a strict secondary
step. -/
theorem rank_drop_of_debt
    {contact oldDebt newDebt : ℕ}
    (hDebt : newDebt < oldDebt) :
    rank contact newDebt < rank contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hDebt⟩)

/-- The contact/debt order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : ContactDebtRank → ContactDebtRank → Prop) :=
  wellFounded_lt

end

end AnchorContactCleaning
end Experimental
end PCRLean
