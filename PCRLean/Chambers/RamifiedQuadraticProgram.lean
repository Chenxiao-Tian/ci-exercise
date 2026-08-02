import Mathlib
import PCRLean.Chambers.RamifiedQuadratic
import PCRLean.Framework.RankedSystem

/-!
# Complete post-anchor program for tame ramified quadratic collision

The explicit model starts from the finite branch equation `z^2-u*t^N` after
the first rank-core blowup.  Repeated collision-cylinder blowups lower `N` by
two.  The even tail is cleared by the final regular branch centre; the odd
tail requires two contact blowups before the same final clearance.

This is a kernel-checked finite affine-chart program for the declared local
model, not a universal scheme-level resolution theorem.
-/

namespace PCRLean.Chambers.RamifiedQuadraticProgram

variable {R : Type*} [CommRing R]

/-- `t`-pivot chart of the first odd-tail contact blowup. -/
theorem oddTail_tPivot (t Z u : R) :
    (t * Z) ^ 2 - u * t = t * (t * Z ^ 2 - u) := by
  ring

/-- `z`-pivot chart of the first odd-tail contact blowup. -/
theorem oddTail_zPivot (z T u : R) :
    z ^ 2 - u * z * T = z * (z - u * T) := by
  ring

/-- First chart of the second contact blowup. -/
theorem oddTail_second_zPivot (z V u : R) :
    z - u * z * V = z * (1 - u * V) := by
  ring

/-- Sibling chart of the second contact blowup. -/
theorem oddTail_second_tPivot (T W u : R) :
    T * W - u * T = T * (W - u) := by
  ring

/-- States of the complete post-anchor branch program.  `secondContact` is the
unique active chart after the first odd-tail contact blowup. -/
inductive State where
  | active (exponent : ℕ)
  | secondContact
  | branchFinal
  | terminal
  deriving DecidableEq, Repr

/-- A rank containing the collision exponent and the finite tail repairs. -/
def rank : State → ℕ
  | .active n => n + 4
  | .secondContact => 2
  | .branchFinal => 1
  | .terminal => 0

/-- Every standard nonempty successor chart of the post-anchor program. -/
inductive Step : State → State → Prop
  | collisionMain (n : ℕ) : Step (.active n) (.active (n + 2))
  | collisionSibling (n : ℕ) : Step .terminal (.active (n + 2))
  | evenTail : Step .branchFinal (.active 0)
  | oddFirstMain : Step .secondContact (.active 1)
  | oddFirstSibling : Step .terminal (.active 1)
  | secondLeft : Step .branchFinal .secondContact
  | secondRight : Step .branchFinal .secondContact
  | finalClear : Step .terminal .branchFinal

/-- Every actual local chart edge strictly lowers the rank. -/
theorem step_decreases {child parent : State} (h : Step child parent) :
    rank child < rank parent := by
  cases h <;> simp [rank] <;> omega

/-- Terminal predicate for the local chart model. -/
def terminal : State → Prop
  | .terminal => True
  | _ => False

/-- Resolution predicate for the local chart model. -/
def resolved : State → Prop := terminal

/-- Every nonterminal local state has a certified successor. -/
theorem progress (s : State) : ¬ terminal s → ∃ t, Step t s := by
  intro h
  cases s with
  | active n =>
      cases n with
      | zero => exact ⟨.branchFinal, Step.evenTail⟩
      | succ n =>
          cases n with
          | zero => exact ⟨.secondContact, Step.oddFirstMain⟩
          | succ n => exact ⟨.active n, Step.collisionMain n⟩
  | secondContact => exact ⟨.branchFinal, Step.secondLeft⟩
  | branchFinal => exact ⟨.terminal, Step.finalClear⟩
  | terminal => exact False.elim (h trivial)

/-- The complete post-anchor local program. -/
def program : PCRLean.Framework.CertifiedProgram where
  State := State
  step := Step
  rank := rank
  step_decreases := step_decreases
  terminal := terminal
  resolved := resolved
  terminal_resolved := by
    intro s hs
    exact hs
  progress := progress

/-- Every tame ramified-quadratic exponent in the declared affine model has a
finite complete post-anchor chart program ending in a resolved local state. -/
theorem active_reaches_resolved (n : ℕ) :
    ∃ finish, Relation.ReflTransGen Step finish (.active n) ∧ resolved finish :=
  program.reaches_resolved (.active n)

end PCRLean.Chambers.RamifiedQuadraticProgram
