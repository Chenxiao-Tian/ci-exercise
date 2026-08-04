import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Tangent rank and contact-cancellation depth

On a projective conormal chamber, a family of regular centres has a common
linear tangent quotient of finite rank and a residual homogeneous
contact-cancellation ideal.  Blowing up the regular reduced carrier has two
strict outcomes:

* the tangent quotient rank drops after a new linear equation appears; or
* at fixed tangent rank, every directional contact depth is shifted down by
  one.

The file proves the exact lexicographic arithmetic.  It does not construct the
contact ideal, prove the graph normal form, or establish the all-chart blowup
shift theorem.
-/

namespace PCRLean
namespace Experimental
namespace ContactCancellationRank

noncomputable section

/-- Lexicographic tangent-rank / contact-depth rank. -/
abbrev Rank := ℕ ×ₗ ℕ

/-- Build the two-coordinate contact rank. -/
def mkRank (tangentRank contactDepth : ℕ) : Rank :=
  toLex (tangentRank, contactDepth)

/-- One chartwise blowup shift removes one unit of positive contact depth. -/
def shiftDepth (contactDepth : ℕ) : ℕ :=
  contactDepth.pred

/-- Positive contact depth strictly decreases under the predecessor shift. -/
theorem shiftDepth_lt
    {contactDepth : ℕ} (hpos : 0 < contactDepth) :
    shiftDepth contactDepth < contactDepth := by
  simpa [shiftDepth] using Nat.pred_lt hpos

/-- At fixed tangent rank, the chartwise contact shift is strict. -/
theorem contact_shift
    {tangentRank contactDepth : ℕ}
    (hpos : 0 < contactDepth) :
    mkRank tangentRank (shiftDepth contactDepth) <
      mkRank tangentRank contactDepth := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, shiftDepth_lt hpos⟩)

/-- A strict tangent-rank drop dominates every possible reset of the contact
coordinate. -/
theorem tangent_rank_drop
    {newRank oldRank newDepth oldDepth : ℕ}
    (hrank : newRank < oldRank) :
    mkRank newRank newDepth < mkRank oldRank oldDepth := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hrank)

/-- The contact rank is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

/-- Finite packet carried by one regular-support contact chamber. -/
structure Packet where
  tangentRank : ℕ
  contactDepth : ℕ

namespace Packet

/-- Rank of a packet. -/
def rank (P : Packet) : Rank :=
  mkRank P.tangentRank P.contactDepth

/-- Shift the contact coordinate by one blowup while retaining the tangent
rank. -/
def shift (P : Packet) : Packet where
  tangentRank := P.tangentRank
  contactDepth := shiftDepth P.contactDepth

/-- A positive contact packet strictly descends after the chartwise shift. -/
theorem shift_rank_lt (P : Packet) (hpos : 0 < P.contactDepth) :
    P.shift.rank < P.rank := by
  exact contact_shift hpos

end Packet

end

end ContactCancellationRank
end Experimental
end PCRLean
