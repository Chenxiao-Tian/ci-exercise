import Mathlib
import PCRLean.Chambers.OddCusp
import PCRLean.Framework.RankedSystem

/-!
# Complete finite chart program for the odd-contact cusp model

This file packages the exact chart identities for `y^2 + s^(2n+1)` into a
finite transition program.  The program includes the repeated active cusp
chart, the terminal sibling chart, and the two boundary-contact blowups for
the smooth tangent tail `y^2+s`.

The result is a kernel-checked theorem about this explicit affine chart model.
It is not a scheme-level theorem for arbitrary singularities.
-/

namespace PCRLean.Chambers.OddCuspProgram

variable {R : Type*} [CommRing R]

/-- In the `s`-pivot chart of the first contact blowup, the strict transform
misses the active boundary corner. -/
theorem firstRepair_sPivot (s Y : R) :
    (s * Y) ^ 2 + s = s * (1 + s * Y ^ 2) := by
  ring

/-- In the `y`-pivot chart of the first contact blowup, the strict transform is
`y+S`; it passes through the crossing of the old and new boundary components. -/
theorem firstRepair_yPivot (y S : R) :
    y ^ 2 + y * S = y * (y + S) := by
  ring

/-- First chart of the second contact blowup. -/
theorem secondRepair_yPivot (y T : R) :
    y + y * T = y * (1 + T) := by
  ring

/-- Sibling chart of the second contact blowup. -/
theorem secondRepair_sPivot (S V : R) :
    S + S * V = S * (1 + V) := by
  ring

/-- States of the complete local chart program.  `secondContact` is the unique
active chart after the first boundary-contact blowup. -/
inductive State where
  | active (debt : ℕ)
  | secondContact
  | terminal
  deriving DecidableEq, Repr

/-- The rank counts the remaining cusp blowups and the two contact blowups. -/
def rank : State → ℕ
  | .active n => n + 2
  | .secondContact => 1
  | .terminal => 0

/-- `Step child parent` records every standard nonempty successor chart. -/
inductive Step : State → State → Prop
  | activeMain (n : ℕ) : Step (.active n) (.active (n + 1))
  | activeSibling (n : ℕ) : Step .terminal (.active (n + 1))
  | firstMain : Step .secondContact (.active 0)
  | firstSibling : Step .terminal (.active 0)
  | secondLeft : Step .terminal .secondContact
  | secondRight : Step .terminal .secondContact

/-- Every actual chart edge strictly lowers the complete local rank. -/
theorem step_decreases {child parent : State} (h : Step child parent) :
    rank child < rank parent := by
  cases h <;> simp [rank]

/-- The local odd-cusp chart tree is well founded. -/
def rankedSystem : PCRLean.Framework.RankedSystem where
  State := State
  step := Step
  rank := rank
  step_decreases := step_decreases

/-- Terminal and resolved coincide for this explicit local chart model. -/
def terminal : State → Prop
  | .terminal => True
  | _ => False

/-- Resolution predicate for the local chart model. -/
def resolved : State → Prop := terminal

/-- Every nonterminal local state has at least one certified successor. -/
theorem progress (s : State) : ¬ terminal s → ∃ t, Step t s := by
  intro h
  cases s with
  | active n =>
      cases n with
      | zero => exact ⟨.secondContact, Step.firstMain⟩
      | succ n => exact ⟨.active n, Step.activeMain n⟩
  | secondContact => exact ⟨.terminal, Step.secondLeft⟩
  | terminal => exact False.elim (h trivial)

/-- The complete local chart program. -/
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

/-- Every state of the complete odd-cusp chart model reaches a resolved leaf. -/
theorem reaches_resolved (start : State) :
    ∃ finish, Relation.ReflTransGen Step finish start ∧ resolved finish :=
  program.reaches_resolved start

/-- In particular, every initial odd-contact debt has a finite complete chart
program ending in a resolved local state. -/
theorem active_reaches_resolved (n : ℕ) :
    ∃ finish, Relation.ReflTransGen Step finish (.active n) ∧ resolved finish :=
  reaches_resolved (.active n)

end PCRLean.Chambers.OddCuspProgram
