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

The resulting conditional resolution theorem is kernel checked. The module
does not postulate that arbitrary positive-characteristic singularities already
provide such a system; constructing it is the remaining geometric theorem.
-/

namespace PCRLean
namespace CartierNoetherMaster

open ResolutionCompiler
open NoetherianPatchingCompiler

noncomputable section

universe u v w x

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- A fully certified geometric realization of one fixed patched program. The
program is an explicit parameter so that the universe of geometric states is
fixed before the remaining certificate fields are elaborated. -/
structure System
    (P : PatchedProgram.{u, v, x} (R := R) (M := M)) where
  Input : Type w
  initState : Input → P.State
  isResolved : P.State → Prop
  terminal_sound : ∀ s, P.terminal s → isResolved s
  step_gated : ∀ {parent child}, P.step parent child →
    Nonempty (CentreGateCertificate P.State parent child)

namespace System

variable {P : PatchedProgram.{u, v, x} (R := R) (M := M)}
variable (S : System (R := R) (M := M) P)

/-- Every input reaches a geometrically resolved state after finitely many
certified steps. -/
theorem every_input_resolves (input : S.Input) :
    ∃ finish : P.State,
      Reaches P.step (S.initState input) finish ∧ S.isResolved finish := by
  obtain ⟨finish, hreach, hterminal⟩ :=
    NoetherianPatchingCompiler.PatchedProgram.terminal_reachable
      P (S.initState input)
  exact ⟨finish, hreach, S.terminal_sound finish hterminal⟩

/-- Every forward geometric step exposes all mandatory centre and transform
gates. -/
theorem every_step_all_gates {parent child : P.State}
    (h : P.step parent child) :
    ∃ C : CentreGateCertificate P.State parent child,
      C.actualFiniteTypeIdeal ∧ C.regularImmersion ∧
      C.markedPermissible ∧ C.passiveSafe ∧ C.boundarySNC ∧
      C.allStandardCharts ∧ C.overlapGluing ∧ C.hereditaryReentry ∧
      C.nonidentity ∧ C.rankDecrease := by
  obtain ⟨C⟩ := CartierNoetherMaster.System.step_gated S h
  exact ⟨C, C.all_gates⟩

/-- No infinite branch can satisfy the fixed-memory/local-drop
classification. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → P.State,
      ∀ n, P.step (f n) (f (n + 1)) :=
  NoetherianPatchingCompiler.PatchedProgram.no_infinite_execution P

end System

/-- The exact universal target, represented as a proposition rather than as a
project axiom. It asks for a patched program and a fully gated realization of
that program for the chosen input language. -/
def UniversalSystemExists (Input : Type w) : Prop :=
  ∃ (P : PatchedProgram.{u, v, x} (R := R) (M := M)),
    ∃ S : System (R := R) (M := M) P, S.Input = Input

end

end CartierNoetherMaster
end PCRLean
