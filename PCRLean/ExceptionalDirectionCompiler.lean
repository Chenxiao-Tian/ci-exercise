import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Exceptional-direction descent compiler

The intended geometric macro is:

1. lower the primary Hilbert--Samuel/marked-order profile; or
2. keep the primary profile and lower the Frobenius height; or
3. keep both and resolve a proper exceptional-direction scheme by a finite
   lower-dimensional macro.

This file proves that any geometric system admitting this trichotomy
terminates.  It does not assert the geometric exceptional-direction dichotomy.
-/

namespace PCRLean
namespace ExceptionalDirectionCompiler

noncomputable section

universe u v

variable {Primary : Type u}
variable (primaryLt : Primary → Primary → Prop)
variable (primaryWf : WellFounded primaryLt)

/-- Primary profile, Frobenius height, and the remaining finite direction
macro height. -/
abbrev Rank := Primary × (Nat × Nat)

/-- Lexicographic order for the three descent modes. -/
def RankLt : Rank (Primary := Primary) → Rank (Primary := Primary) → Prop :=
  Prod.Lex primaryLt (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))

/-- The exceptional-direction rank is well founded. -/
theorem rankLt_wellFounded :
    WellFounded (RankLt (Primary := Primary) primaryLt) := by
  exact WellFounded.prod_lex primaryWf
    (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- The three accepted geometric descent modes.  The first argument is the
child rank and the second is the parent rank. -/
inductive RankStep :
    Rank (Primary := Primary) → Rank (Primary := Primary) → Prop
  | primaryDrop
      {pChild pParent : Primary}
      {eChild eParent dChild dParent : Nat}
      (hp : primaryLt pChild pParent) :
      RankStep (pChild, (eChild, dChild)) (pParent, (eParent, dParent))
  | frobeniusDrop
      {p : Primary} {eChild eParent dChild dParent : Nat}
      (he : eChild < eParent) :
      RankStep (p, (eChild, dChild)) (p, (eParent, dParent))
  | directionDrop
      {p : Primary} {e dChild dParent : Nat}
      (hd : dChild < dParent) :
      RankStep (p, (e, dChild)) (p, (e, dParent))

/-- Every accepted mode strictly lowers the compiled lexicographic rank. -/
theorem rankStep_decreases
    {child parent : Rank (Primary := Primary)}
    (h : RankStep primaryLt child parent) :
    RankLt primaryLt child parent := by
  cases h with
  | primaryDrop hp => exact Prod.Lex.left _ _ hp
  | frobeniusDrop he =>
      exact Prod.Lex.right _ (Prod.Lex.left _ _ he)
  | directionDrop hd =>
      exact Prod.Lex.right _ (Prod.Lex.right _ hd)

/-- The bare trichotomy relation is well founded. -/
theorem rankStep_wellFounded :
    WellFounded (RankStep (Primary := Primary) primaryLt) := by
  exact Subrelation.wf (rankStep_decreases primaryLt)
    (rankLt_wellFounded primaryLt primaryWf)

/-- A geometric program classified by exceptional-direction descent. -/
structure Program where
  State : Type v
  step : State → State → Prop
  terminal : State → Prop
  primary : State → Primary
  frobeniusHeight : State → Nat
  directionHeight : State → Nat
  classify : ∀ {parent child}, step parent child →
    RankStep primaryLt
      (primary child, (frobeniusHeight child, directionHeight child))
      (primary parent, (frobeniusHeight parent, directionHeight parent))
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace Program

variable (P : Program (Primary := Primary) primaryLt)

/-- The compiled rank of a geometric state. -/
def compiledRank (s : P.State) : Rank (Primary := Primary) :=
  (P.primary s, (P.frobeniusHeight s, P.directionHeight s))

/-- Every forward geometric transition strictly decreases the compiled rank. -/
theorem step_decreases {parent child : P.State} (h : P.step parent child) :
    RankLt primaryLt (P.compiledRank child) (P.compiledRank parent) := by
  exact rankStep_decreases primaryLt (P.classify h)

/-- Compile the trichotomy program into the general verified termination
backend. -/
def toProgram : ResolutionCompiler.Program where
  State := P.State
  Rank := Rank (Primary := Primary)
  step := P.step
  terminal := P.terminal
  rank := P.compiledRank
  lt := RankLt primaryLt
  wf := rankLt_wellFounded primaryLt primaryWf
  decreases := P.step_decreases
  progress := P.progress

/-- Every state reaches a terminal state in finitely many certified steps. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t := by
  exact P.toProgram primaryWf |>.terminal_reachable s

/-- No infinite branch can satisfy the geometric trichotomy. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) := by
  exact P.toProgram primaryWf |>.no_infinite_execution

end Program

end

end ExceptionalDirectionCompiler
end PCRLean
