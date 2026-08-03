import Mathlib
import PCRLean.Experimental.NoetherianCentreWordStack
import PCRLean.ResolutionCompiler

/-!
# Experimental three-layer termination compiler

A positive-characteristic resolution transition may improve for three distinct
reasons:

1. it creates a genuinely new trace in one fixed Noetherian ancestor module;
2. at fixed trace memory, it consumes at least one atom of a fixed finite
   ancestor-source ledger;
3. at fixed memory and source ledger, it replaces one centre-word obligation by
   finitely many strictly lower-height obligations.

The nested lexicographic rank combining these mechanisms is well founded.  This
file compiles any geometric program admitting that trichotomy into the generic
verified termination backend.  It does not prove that arbitrary blowup steps
satisfy the trichotomy; that remains the geometric birth and hereditary-reentry
problem.
-/

namespace PCRLean
namespace Experimental
namespace ThreeLayerTerminationCompiler

noncomputable section

universe u v w

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- Inner finite rank: remaining ancestor-source atoms, followed by the
multiset of unresolved centre-word heights. -/
abbrev InnerRank := Nat × Multiset Nat

/-- Full rank: fixed-ancestor Noetherian trace memory, finite source debt, and
centre-word multiset. -/
abbrev Rank := Submodule R M × InnerRank

/-- At fixed trace memory, first consume unused source atoms; if that count is
unchanged, strictly refine the centre-word multiset. -/
def InnerLt : InnerRank → InnerRank → Prop :=
  Prod.Lex (fun a b : Nat => a < b)
    Multiset.IsDershowitzMannaLT

/-- Strict trace-memory enlargement is primary.  At unchanged memory, use the
finite source/centre-word rank. -/
def RankLt : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop :=
  Prod.Lex (fun C D : Submodule R M => C > D) InnerLt

/-- The finite source/centre-word rank is well founded. -/
theorem innerLt_wellFounded : WellFounded InnerLt := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf
    Multiset.wellFounded_isDershowitzMannaLT

/-- The full three-layer rank is well founded. -/
theorem rankLt_wellFounded : WellFounded (RankLt (R := R) (M := M)) := by
  exact WellFounded.prod_lex
    (IsNoetherian.wf (R := R) (M := M)
      (inferInstance : IsNoetherian R M))
    innerLt_wellFounded

/-- Accepted rank transitions.  The first argument is the child rank and the
second is the parent rank. -/
inductive RankStep : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop
  | newTrace
      {C D : Submodule R M}
      {childInner parentInner : InnerRank}
      (hCD : D > C) :
      RankStep (D, childInner) (C, parentInner)
  | freshBirth
      {C : Submodule R M}
      {childUnused parentUnused : Nat}
      {childWord parentWord : Multiset Nat}
      (hunused : childUnused < parentUnused) :
      RankStep (C, (childUnused, childWord))
        (C, (parentUnused, parentWord))
  | refineWord
      {C : Submodule R M}
      {unused : Nat}
      {childWord parentWord : Multiset Nat}
      (hword : NoetherianCentreWordStack.WordExpansion childWord parentWord) :
      RankStep (C, (unused, childWord))
        (C, (unused, parentWord))

/-- Every accepted transition strictly decreases the nested rank. -/
theorem rankStep_decreases
    {child parent : Rank (R := R) (M := M)}
    (h : RankStep child parent) : RankLt child parent := by
  cases h with
  | newTrace hCD =>
      exact Prod.Lex.left _ _ hCD
  | freshBirth hunused =>
      exact Prod.Lex.right _ (Prod.Lex.left _ _ hunused)
  | refineWord hword =>
      exact Prod.Lex.right _
        (Prod.Lex.right _
          (NoetherianCentreWordStack.wordExpansion_isDershowitzMannaLT hword))

/-- The accepted three-layer transition relation is well founded. -/
theorem rankStep_wellFounded :
    WellFounded (RankStep (R := R) (M := M)) := by
  exact Subrelation.wf rankStep_decreases rankLt_wellFounded

/-- A geometric program equipped with the complete three-way classification.
The substantive future theorem is `classify`: every actual forward blowup step
must be a new independent trace, a fresh finite-source birth, or a lower centre-
word refinement. -/
structure Program where
  State : Type w
  step : State → State → Prop
  terminal : State → Prop
  memory : State → Submodule R M
  unusedSources : State → Nat
  obligations : State → Multiset Nat
  classify : ∀ {parent child}, step parent child →
    RankStep
      (memory child, (unusedSources child, obligations child))
      (memory parent, (unusedSources parent, obligations parent))
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace Program

variable (P : Program (R := R) (M := M))

/-- Compiled three-layer rank of a geometric state. -/
def compiledRank (s : P.State) : Rank (R := R) (M := M) :=
  (P.memory s, (P.unusedSources s, P.obligations s))

/-- Every classified geometric transition strictly lowers the compiled rank. -/
theorem step_decreases {parent child : P.State} (h : P.step parent child) :
    RankLt (P.compiledRank child) (P.compiledRank parent) := by
  exact rankStep_decreases (P.classify h)

/-- Compile the geometric program into the generic verified termination
backend. -/
def toResolutionProgram : ResolutionCompiler.Program where
  State := P.State
  Rank := Rank (R := R) (M := M)
  step := P.step
  terminal := P.terminal
  rank := P.compiledRank
  lt := RankLt (R := R) (M := M)
  wf := rankLt_wellFounded (R := R) (M := M)
  decreases := P.step_decreases
  progress := P.progress

/-- Every state reaches a terminal state after finitely many accepted steps. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t := by
  exact P.toResolutionProgram.terminal_reachable s

/-- No infinite execution can satisfy the three-layer classification. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) :=
  P.toResolutionProgram.no_infinite_execution

end Program

end

end ThreeLayerTerminationCompiler
end Experimental
end PCRLean
