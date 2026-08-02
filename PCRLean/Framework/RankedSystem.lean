import Mathlib

/-!
# Abstract certificate backend for terminating resolution programs

This module proves the logical termination theorem used by the candidate
resolution architecture.  It does not construct geometric centres.  Instead,
it states precisely what a geometric front end must provide: a transition
relation, a natural-valued strict rank, a no-dead-end condition, and terminal
correctness.
-/

namespace PCRLean.Framework

/-- A transition system whose every edge strictly lowers a natural-valued
rank.  The relation is oriented `step child parent`. -/
structure RankedSystem where
  State : Type*
  step : State → State → Prop
  rank : State → ℕ
  step_decreases : ∀ {child parent}, step child parent → rank child < rank parent

namespace RankedSystem

variable (S : RankedSystem)

/-- Every certified transition relation is a subrelation of the inverse image
of `<` under the rank map. -/
theorem step_sub_rank :
    ∀ {child parent}, S.step child parent →
      InvImage (· < ·) S.rank child parent :=
  fun h => S.step_decreases h

/-- A ranked transition system admits no infinite descending branch. -/
theorem step_wellFounded : WellFounded S.step := by
  have hNat : WellFounded ((· < ·) : ℕ → ℕ → Prop) := Nat.lt_wfRel.wf
  apply (hNat.onFun S.rank).mono
  intro child parent hstep
  exact S.step_decreases hstep

/-- Equivalent no-infinite-chain formulation. -/
theorem no_infinite_chain :
    IsEmpty {f : ℕ → S.State // ∀ n, S.step (f (n + 1)) (f n)} :=
  wellFounded_iff_isEmpty_descending_chain.mp S.step_wellFounded

/-- No state lies on a nonempty certified cycle. -/
theorem no_cycle (s : S.State) : ¬ Relation.TransGen S.step s s := by
  have hIrr : Std.Irrefl (Relation.TransGen S.step) :=
    S.step_wellFounded.transGen.irrefl
  exact hIrr.irrefl s

end RankedSystem

/-- A ranked program with a terminal predicate and enough geometric coverage
to exclude dead ends. -/
structure CertifiedProgram extends RankedSystem where
  terminal : State → Prop
  resolved : State → Prop
  terminal_resolved : ∀ {s}, terminal s → resolved s
  progress : ∀ s, ¬ terminal s → ∃ t, step t s

namespace CertifiedProgram

variable (P : CertifiedProgram)

/-- The transition relation of a certified program is well founded. -/
theorem step_wellFounded : WellFounded P.step :=
  P.toRankedSystem.step_wellFounded

/-- Every state has a finite certified path to a terminal state. -/
theorem reaches_terminal (start : P.State) :
    ∃ finish, Relation.ReflTransGen P.step finish start ∧ P.terminal finish := by
  induction start using P.step_wellFounded.induction with
  | h state ih =>
      by_cases hterm : P.terminal state
      · exact ⟨state, Relation.ReflTransGen.refl, hterm⟩
      · obtain ⟨child, hstep⟩ := P.progress state hterm
        obtain ⟨finish, hpath, hfinish⟩ := ih child hstep
        exact ⟨finish, hpath.tail hstep, hfinish⟩

/-- Consequently every state has a finite certified path to a resolved state. -/
theorem reaches_resolved (start : P.State) :
    ∃ finish, Relation.ReflTransGen P.step finish start ∧ P.resolved finish := by
  obtain ⟨finish, hpath, hterminal⟩ := P.reaches_terminal start
  exact ⟨finish, hpath, P.terminal_resolved hterminal⟩

end CertifiedProgram

end PCRLean.Framework
