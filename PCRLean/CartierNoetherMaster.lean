import Mathlib
import PCRLean.ResolutionCompiler
import PCRLean.NoetherianPatchingCompiler

/-!
# Cartier--Noether conditional master theorem

This module packages the exact logical content of the history-inspired
architecture. A geometric system is complete once every nonterminal state has
an actual gated successor and every successor is classified either as a new
independent trace in one fixed Noetherian ancestor module or as a strict local
rank drop with unchanged trace memory.

The resulting resolution theorem is fully kernel checked. The module does not
postulate that arbitrary positive-characteristic singularities already admit
such a system; constructing it is the remaining geometric theorem.
-/

namespace PCRLean
namespace CartierNoetherMaster

open ResolutionCompiler
open NoetherianPatchingCompiler

noncomputable section

universe u v w

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- A fully certified geometric system using the patched Noetherian rank. -/
structure System where
  Input : Type w
  P : PatchedProgram (R := R) (M := M)
  initState : Input → P.State
  isResolved : P.State → Prop
  terminal_sound : ∀ s, P.terminal s → isResolved s
  step_gated : ∀ {child parent}, P.step child parent →
    Nonempty (CentreGateCertificate P.State child parent)

namespace System

variable (S : System (R := R) (M := M))

/-- Every input reaches a geometrically resolved state after finitely many
certified steps. -/
theorem every_input_resolves (x : S.Input) :
    ∃ finish,
      Reaches S.P.step (S.initState x) finish ∧ S.isResolved finish := by
  obtain ⟨finish, hreach, hterminal⟩ :=
    S.P.terminal_reachable (S.initState x)
  exact ⟨finish, hreach, S.terminal_sound finish hterminal⟩

/-- Every geometric step exposes all mandatory centre and transform gates. -/
theorem every_step_all_gates {child parent : S.P.State}
    (h : S.P.step child parent) :
    ∃ C : CentreGateCertificate S.P.State child parent,
      C.actualFiniteTypeIdeal ∧ C.regularImmersion ∧
      C.markedPermissible ∧ C.passiveSafe ∧ C.boundarySNC ∧
      C.allStandardCharts ∧ C.overlapGluing ∧ C.hereditaryReentry ∧
      C.nonidentity ∧ C.rankDecrease := by
  obtain ⟨C⟩ := S.step_gated h
  exact ⟨C, C.all_gates⟩

/-- No infinite branch can satisfy the fixed-memory/local-drop
classification. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → S.P.State,
      ∀ n, S.P.step (f n) (f (n + 1)) :=
  S.P.no_infinite_execution

end System

/-- The exact universal target, represented as a proposition rather than as a
project axiom. -/
def UniversalSystemExists (Input : Type w) : Prop :=
  ∃ S : System (R := R) (M := M), S.Input = Input

end

end CartierNoetherMaster
end PCRLean
