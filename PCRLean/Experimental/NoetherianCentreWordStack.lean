import Mathlib
import Mathlib.Data.Multiset.DershowitzManna
import PCRLean.ResolutionCompiler

/-!
# Experimental Noetherian centre-word rewrite stack

A centre-word obligation is assigned a natural-number height.  One obligation
of height `h` may be replaced by finitely many obligations, each of height
strictly smaller than `h`.  The resulting stack transition is exactly a special
case of the Dershowitz--Manna multiset order and is therefore well founded.

Coupling this stack with one fixed Noetherian ancestor-memory module gives a
rank that permits either a genuine new trace or a finite lower-height macro
expansion.  This is a termination backend only: geometry must still prove that
every actual centre-word transition has one of these two forms.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianCentreWordStack

noncomputable section

universe u v w

/-- Replace one unresolved obligation by finitely many strictly lower-height
obligations, leaving all unrelated obligations unchanged. -/
def WordExpansion (child parent : Multiset Nat) : Prop :=
  ∃ common spawned h,
    child = common + spawned ∧
    parent = common + {h} ∧
    ∀ n ∈ spawned, n < h

/-- Every centre-word expansion is a Dershowitz--Manna multiset decrease. -/
theorem wordExpansion_isDershowitzMannaLT
    {child parent : Multiset Nat}
    (h : WordExpansion child parent) :
    child.IsDershowitzMannaLT parent := by
  rcases h with ⟨common, spawned, height, hchild, hparent, hlower⟩
  refine ⟨common, spawned, {height}, ?_, hchild, hparent, ?_⟩
  · simp
  · intro n hn
    exact ⟨height, by simp, hlower n hn⟩

/-- The bare centre-word expansion relation is well founded. -/
theorem wordExpansion_wellFounded : WellFounded WordExpansion := by
  exact Subrelation.wf wordExpansion_isDershowitzMannaLT
    Multiset.wellFounded_isDershowitzMannaLT

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- Fixed-ancestor Noetherian memory together with a multiset of unresolved
centre-word heights. -/
abbrev Rank := Submodule R M × Multiset Nat

/-- New independent memory is primary; at fixed memory, the centre-word stack
must decrease in the Dershowitz--Manna order. -/
def RankLt : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop :=
  Prod.Lex (fun C D : Submodule R M => C > D)
    Multiset.IsDershowitzMannaLT

/-- The combined Noetherian/centre-word rank is well founded. -/
theorem rankLt_wellFounded : WellFounded (RankLt (R := R) (M := M)) := by
  exact WellFounded.prod_lex
    (IsNoetherian.wf (R := R) (M := M)
      (inferInstance : IsNoetherian R M))
    Multiset.wellFounded_isDershowitzMannaLT

/-- Accepted stack transitions.  The first rank is the child and the second is
the parent. -/
inductive RankStep : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop
  | newTrace {C D : Submodule R M} {childWord parentWord : Multiset Nat}
      (hCD : D > C) : RankStep (D, childWord) (C, parentWord)
  | refineWord {C : Submodule R M} {childWord parentWord : Multiset Nat}
      (hword : WordExpansion childWord parentWord) :
      RankStep (C, childWord) (C, parentWord)

/-- Every accepted transition decreases the combined rank. -/
theorem rankStep_decreases
    {child parent : Rank (R := R) (M := M)}
    (h : RankStep child parent) : RankLt child parent := by
  cases h with
  | newTrace hCD => exact Prod.Lex.left _ _ hCD
  | refineWord hword =>
      exact Prod.Lex.right _ (wordExpansion_isDershowitzMannaLT hword)

/-- The accepted rank-step relation is well founded. -/
theorem rankStep_wellFounded :
    WellFounded (RankStep (R := R) (M := M)) := by
  exact Subrelation.wf rankStep_decreases rankLt_wellFounded

/-- A geometric rewrite program classified by actual new traces or finite
lower-height centre-word expansion. -/
structure Program where
  State : Type w
  step : State → State → Prop
  terminal : State → Prop
  memory : State → Submodule R M
  obligations : State → Multiset Nat
  classify : ∀ {parent child}, step parent child →
    RankStep (memory child, obligations child)
      (memory parent, obligations parent)
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace Program

variable (P : Program (R := R) (M := M))

/-- Compiled stack rank of one geometric state. -/
def compiledRank (s : P.State) : Rank (R := R) (M := M) :=
  (P.memory s, P.obligations s)

/-- Every geometric rewrite decreases the compiled stack rank. -/
theorem step_decreases {parent child : P.State} (h : P.step parent child) :
    RankLt (P.compiledRank child) (P.compiledRank parent) := by
  exact rankStep_decreases (P.classify h)

/-- Compile the centre-word stack into the generic verified backend. -/
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

/-- Every state reaches a terminal state after finitely many accepted rewrite
steps. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t := by
  exact P.toResolutionProgram.terminal_reachable s

/-- No infinite centre-word execution satisfies the accepted classification. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) :=
  P.toResolutionProgram.no_infinite_execution

end Program

end

end NoetherianCentreWordStack
end Experimental
end PCRLean