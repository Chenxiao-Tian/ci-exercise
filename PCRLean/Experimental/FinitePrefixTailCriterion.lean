import Mathlib

/-!
# Finite prefix plus eventual tail implies the full graded condition

The projective Rees--Serre criterion has a simple logical compiler.  A finite
graded module is controlled by a bounded window of low degrees together with an
eventual projective tail.  Once the geometric theorem supplies the cutoff and
the two certificates, every degree is covered.

This file proves only the exact finite-prefix/tail coverage.  It does not prove
Serre vanishing, cohomology and base change, projective flattening, or the
normal-flatness theorem for an associated graded module.
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

/-- Every degree at or above the lower bound is covered by exactly one of the
finite-window or projective-tail branches. -/
theorem all_degrees (P : Packet Good) :
    ∀ n, P.lower ≤ n → Good n := by
  intro n hn
  by_cases hcut : n < P.cutoff
  · exact P.finiteWindow n hn hcut
  · exact P.projectiveTail n (Nat.le_of_not_gt hcut)

/-- Pointwise form useful to a successor-state compiler. -/
theorem degree (P : Packet Good) {n : ℕ} (hn : P.lower ≤ n) :
    Good n :=
  P.all_degrees n hn

end Packet

/-- Direct constructor when the cutoff is already fixed by a geometric
certificate. -/
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
