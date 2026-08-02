import Mathlib
import PCRLean.Chambers.PurelyInseparable
import PCRLean.Framework.RankedSystem

/-!
# Finite collision program for a purely inseparable quadratic tail

For the explicit no-linear-term family `z^2 + u*t^(2d)`, each active
collision-cylinder chart lowers `d+1` to `d`; the sibling chart is terminal on
the exceptional fibre.  At depth zero the program returns a typed radicial
frontier.  It does not assert that an arbitrary radicial frontier has a regular
permissible centre.
-/

namespace PCRLean.Chambers.PurelyInseparableProgram

/-- States of the forced collision phase. -/
inductive State where
  | active (depth : ℕ)
  | radicialFrontier
  | terminalSibling
  deriving DecidableEq, Repr

/-- Natural rank for the finite forced collision phase. -/
def rank : State → ℕ
  | .active d => d + 1
  | .radicialFrontier => 0
  | .terminalSibling => 0

/-- Every nonempty standard successor chart. -/
inductive Step : State → State → Prop
  | collisionMain (d : ℕ) : Step (.active d) (.active (d + 1))
  | collisionSibling (d : ℕ) : Step .terminalSibling (.active (d + 1))
  | radicialExit : Step .radicialFrontier (.active 0)

/-- Every chart edge strictly lowers the phase rank. -/
theorem step_decreases {child parent : State} (h : Step child parent) :
    rank child < rank parent := by
  cases h <;> simp [rank] <;> omega

/-- Terminal means either the harmless sibling chart or the explicit radicial
frontier. -/
def classifiedExit : State → Prop
  | .radicialFrontier => True
  | .terminalSibling => True
  | _ => False

/-- Every nonexit state has an accepted successor. -/
theorem progress (s : State) : ¬ classifiedExit s → ∃ t, Step t s := by
  intro h
  cases s with
  | active d =>
      cases d with
      | zero => exact ⟨.radicialFrontier, Step.radicialExit⟩
      | succ d => exact ⟨.active d, Step.collisionMain d⟩
  | radicialFrontier => exact False.elim (h trivial)
  | terminalSibling => exact False.elim (h trivial)

/-- The complete finite collision classifier. -/
def program : PCRLean.Framework.CertifiedProgram where
  State := State
  step := Step
  rank := rank
  step_decreases := step_decreases
  terminal := classifiedExit
  resolved := classifiedExit
  terminal_resolved := by
    intro s hs
    exact hs
  progress := progress

/-- Every initial even collision depth reaches a terminal sibling chart or the
typed radicial frontier in finitely many steps. -/
theorem active_reaches_radicial_exit (d : ℕ) :
    ∃ finish, Relation.ReflTransGen Step finish (.active d) ∧
      classifiedExit finish :=
  program.reaches_resolved (.active d)

end PCRLean.Chambers.PurelyInseparableProgram
