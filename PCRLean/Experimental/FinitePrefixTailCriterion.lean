import Mathlib

/-!
# Finite prefix plus eventual projective tail

A finite graded module over a relative symmetric algebra is controlled by a
bounded window of low degrees together with an eventual Serre tail.  Once the
geometric theorem supplies the cutoff and the two certificates, every degree is
covered.

This file proves only the exact finite-prefix/tail logical compiler.  It does
not prove relative Serre vanishing, cohomology and base change, projective
flatification, or the comparison with an actual associated-graded transform.
-/

namespace PCRLean
namespace Experimental
namespace FinitePrefixTailCriterion

noncomputable section

/-- A finite window and an eventual tail certificate for a degreewise
property. -/
structure Packet (Good : ℕ → Prop) where
  lower : ℕ
  cutoff : ℕ
  lower_le_cutoff : lower ≤ cutoff
  finiteWindow : ∀ n, lower ≤ n → n < cutoff → Good n
  projectiveTail : ∀ n, cutoff ≤ n → Good n

namespace Packet

variable {Good : ℕ → Prop}

/-- Every degree at or above the lower bound is covered by the finite window or
by the eventual projective tail. -/
theorem all_degrees (P : Packet Good) :
    ∀ n, P.lower ≤ n → Good n := by
  intro n hn
  by_cases hcut : n < P.cutoff
  · exact P.finiteWindow n hn hcut
  · exact P.projectiveTail n (Nat.le_of_not_gt hcut)

/-- Pointwise form consumed by a successor-state compiler. -/
theorem degree (P : Packet Good) {n : ℕ} (hn : P.lower ≤ n) :
    Good n :=
  P.all_degrees n hn

end Packet

/-- Direct form when the cutoff is supplied independently. -/
theorem all_of_window_of_tail
    (Good : ℕ → Prop) {lower cutoff : ℕ}
    (hwindow : ∀ n, lower ≤ n → n < cutoff → Good n)
    (htail : ∀ n, cutoff ≤ n → Good n) :
    ∀ n, lower ≤ n → Good n := by
  intro n hn
  by_cases hcut : n < cutoff
  · exact hwindow n hn hcut
  · exact htail n (Nat.le_of_not_gt hcut)

end

end FinitePrefixTailCriterion
end Experimental
end PCRLean
