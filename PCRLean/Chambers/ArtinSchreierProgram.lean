import Mathlib
import PCRLean.Chambers.ArtinSchreier
import PCRLean.Framework.RankedSystem

/-!
# Finite classifier for the Artin-Schreier quadratic collision chamber

The active collision chart lowers `(m+1,r+2)` to `(m,r)`.  The process exits
in exactly one of three typed tails: etale (`m=0`), wild odd (`r=1`), or even
radicial (`r=0`).  The wild odd tail is followed by the finite contact-repair
and branch-clearance program.  The even radicial tail is deliberately returned
as a typed frontier, not mislabelled as resolved geometry.
-/

namespace PCRLean.Chambers.ArtinSchreierProgram

/-- States of the post-anchor collision classifier. -/
inductive State where
  | active (m r : ℕ)
  | wildSecondContact
  | branchFinal
  | radicialFrontier
  | terminal
  deriving DecidableEq, Repr

/-- A simple rank for the finite classifier and its wild-tail repairs. -/
def rank : State → ℕ
  | .active m r => m + r + 4
  | .wildSecondContact => 2
  | .branchFinal => 1
  | .radicialFrontier => 0
  | .terminal => 0

/-- Every standard successor chart of the declared classifier. -/
inductive Step : State → State → Prop
  | collisionMain (m r : ℕ) : Step (.active m r) (.active (m + 1) (r + 2))
  | collisionSibling (m r : ℕ) : Step .terminal (.active (m + 1) (r + 2))
  | etaleTail (r : ℕ) : Step .branchFinal (.active 0 r)
  | wildFirstMain (m : ℕ) : Step .wildSecondContact (.active (m + 1) 1)
  | wildFirstSibling (m : ℕ) : Step .terminal (.active (m + 1) 1)
  | evenRadicial (m : ℕ) : Step .radicialFrontier (.active (m + 1) 0)
  | wildSecondLeft : Step .branchFinal .wildSecondContact
  | wildSecondRight : Step .branchFinal .wildSecondContact
  | finalClear : Step .terminal .branchFinal

/-- Every classifier edge strictly lowers the natural rank. -/
theorem step_decreases {child parent : State} (h : Step child parent) :
    rank child < rank parent := by
  cases h <;> simp [rank] <;> omega

/-- A successful classifier exit is either a resolved terminal chart or the
explicit even-radicial frontier. -/
def classifiedExit : State → Prop
  | .radicialFrontier => True
  | .terminal => True
  | _ => False

/-- Every nonexit state has at least one certified successor. -/
theorem progress (s : State) : ¬ classifiedExit s → ∃ t, Step t s := by
  intro h
  cases s with
  | active m r =>
      cases m with
      | zero => exact ⟨.branchFinal, Step.etaleTail r⟩
      | succ m =>
          cases r with
          | zero => exact ⟨.radicialFrontier, Step.evenRadicial m⟩
          | succ r =>
              cases r with
              | zero => exact ⟨.wildSecondContact, Step.wildFirstMain m⟩
              | succ r => exact ⟨.active m r, Step.collisionMain m r⟩
  | wildSecondContact => exact ⟨.branchFinal, Step.wildSecondLeft⟩
  | branchFinal => exact ⟨.terminal, Step.finalClear⟩
  | radicialFrontier => exact False.elim (h trivial)
  | terminal => exact False.elim (h trivial)

/-- The complete finite collision classifier.  Here `resolved` means
"classified as a terminal branch or an explicit radicial frontier". -/
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

/-- Every pair `(m,r)` reaches a terminal branch or the typed even-radicial
frontier in finitely many collision/repair steps. -/
theorem active_reaches_classified_exit (m r : ℕ) :
    ∃ finish, Relation.ReflTransGen Step finish (.active m r) ∧ classifiedExit finish :=
  program.reaches_resolved (.active m r)

end PCRLean.Chambers.ArtinSchreierProgram
