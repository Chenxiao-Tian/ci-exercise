import Mathlib
import PCRLean.Chambers.FrobeniusContent
import PCRLean.Framework.RankedSystem

/-!
# Finite exit program for the principal anchored Frobenius-content chamber

The active chart lowers the content depth by one, every sibling chart is
terminal for the declared marked packet, and depth zero exits to a lower
packet.  The terminal predicate here means "terminal or escaped to an earlier
certified packet", not general geometric resolution.
-/

namespace PCRLean.Chambers.FrobeniusContentProgram

/-- States of the restricted anchored-content program. -/
inductive State where
  | active (depth : ℕ)
  | lowerPacket
  | terminalSibling
  deriving DecidableEq, Repr

/-- Remaining anchored content depth. -/
def rank : State → ℕ
  | .active n => n + 1
  | .lowerPacket => 0
  | .terminalSibling => 0

/-- Every standard successor chart in the restricted chamber. -/
inductive Step : State → State → Prop
  | activeMain (n : ℕ) : Step (.active n) (.active (n + 1))
  | activeSibling (n : ℕ) : Step .terminalSibling (.active (n + 1))
  | baseExit : Step .lowerPacket (.active 0)

/-- Every chart edge strictly lowers the content-program rank. -/
theorem step_decreases {child parent : State} (h : Step child parent) :
    rank child < rank parent := by
  cases h <;> simp [rank]

/-- Terminal-or-lower-packet predicate for this chamber. -/
def terminal : State → Prop
  | .active _ => False
  | .lowerPacket => True
  | .terminalSibling => True

/-- Successful exit predicate for the restricted chamber. -/
def resolved : State → Prop := terminal

/-- Every nonterminal content state has a certified successor. -/
theorem progress (s : State) : ¬ terminal s → ∃ t, Step t s := by
  intro h
  cases s with
  | active n =>
      cases n with
      | zero => exact ⟨.lowerPacket, Step.baseExit⟩
      | succ n => exact ⟨.active n, Step.activeMain n⟩
  | lowerPacket => exact False.elim (h trivial)
  | terminalSibling => exact False.elim (h trivial)

/-- The finite restricted content program. -/
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

/-- Every finite anchored content depth exits the restricted chamber. -/
theorem active_reaches_exit (n : ℕ) :
    ∃ finish, Relation.ReflTransGen Step finish (.active n) ∧ resolved finish :=
  program.reaches_resolved (.active n)

end PCRLean.Chambers.FrobeniusContentProgram
