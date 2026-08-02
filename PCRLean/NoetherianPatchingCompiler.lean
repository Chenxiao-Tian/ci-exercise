import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Noetherian patching compiler

This file combines two historically distinct termination mechanisms.
A geometric step may either enlarge one fixed Noetherian ancestor-memory module
(the Hilbert--Noether mechanism), or keep that memory unchanged and decrease a
finite local rank (the Hironaka/finite-centre-word mechanism). The resulting
lexicographic relation is well founded.

The theorem is a genuine termination compiler. It does not assert that every
positive-characteristic blowup step satisfies the required classification;
that is the geometric birth-realization theorem.
-/

namespace PCRLean
namespace NoetherianPatchingCompiler

noncomputable section

universe u v w

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- Outer Noetherian memory together with an inner finite macro rank. -/
abbrev Rank := Submodule R M × Nat

/-- Lexicographic descent: strict memory enlargement is primary; if memory is
unchanged, the local natural-number rank must decrease. -/
def RankLt : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop :=
  Prod.Lex (fun C D : Submodule R M => C > D) (fun a b : Nat => a < b)

/-- The patched rank is well founded by Noetherianity and natural-number
well-foundedness. -/
theorem rankLt_wellFounded : WellFounded (RankLt (R := R) (M := M)) := by
  exact WellFounded.prod_lex
    (IsNoetherian.wf (R := R) (M := M)
      (inferInstance : IsNoetherian R M))
    Nat.lt_wfRel.wf

/-- One of the two certified transition modes. -/
inductive RankStep : Rank (R := R) (M := M) → Rank (R := R) (M := M) → Prop
  | newTrace {C D : Submodule R M} {n m : Nat}
      (hCD : D > C) : RankStep (D, n) (C, m)
  | localDrop {C : Submodule R M} {n m : Nat}
      (hnm : n < m) : RankStep (C, n) (C, m)

/-- Every accepted transition decreases the patched rank. -/
theorem rankStep_decreases {child parent : Rank (R := R) (M := M)}
    (h : RankStep child parent) : RankLt child parent := by
  cases h with
  | newTrace hCD => exact Prod.Lex.left _ _ hCD
  | localDrop hnm => exact Prod.Lex.right _ hnm

/-- The bare rank-step relation is well founded. -/
theorem rankStep_wellFounded :
    WellFounded (RankStep (R := R) (M := M)) := by
  exact Subrelation.wf rankStep_decreases rankLt_wellFounded

/-- A geometric program equipped with a fixed Noetherian memory and a finite
local rank. `classify` is the substantive bridge: every actual geometric step
must either create a genuinely independent ancestor trace or pay the local
rank without changing memory. -/
structure PatchedProgram where
  State : Type w
  step : State → State → Prop
  terminal : State → Prop
  memory : State → Submodule R M
  localRank : State → Nat
  classify : ∀ {child parent}, step child parent →
    RankStep (memory child, localRank child) (memory parent, localRank parent)
  progress : ∀ s, ¬ terminal s → ∃ t, step t s

namespace PatchedProgram

variable (P : PatchedProgram (R := R) (M := M))

/-- The compiled rank of a geometric state. -/
def compiledRank (s : P.State) : Rank (R := R) (M := M) :=
  (P.memory s, P.localRank s)

/-- Every geometric step strictly decreases the compiled lexicographic rank. -/
theorem step_decreases {child parent : P.State} (h : P.step child parent) :
    RankLt (P.compiledRank child) (P.compiledRank parent) := by
  exact rankStep_decreases (P.classify h)

/-- The patched program compiled into the general verified termination
backend. Terminal soundness is deliberately supplied by a later geometric
layer rather than hidden here. -/
def toProgram : ResolutionCompiler.Program where
  State := P.State
  Rank := Rank (R := R) (M := M)
  step := P.step
  terminal := P.terminal
  rank := P.compiledRank
  lt := RankLt (R := R) (M := M)
  wf := rankLt_wellFounded (R := R) (M := M)
  decreases := P.step_decreases
  progress := P.progress

/-- Every state reaches a terminal state in finitely many steps. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t := by
  exact P.toProgram.terminal_reachable s

/-- No infinite execution branch can satisfy the patched classification. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) :=
  P.toProgram.no_infinite_execution

end PatchedProgram

end

end NoetherianPatchingCompiler
end PCRLean
