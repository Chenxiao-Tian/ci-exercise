import Mathlib
import PCRLean.ResolutionCompiler

namespace PCRLean
namespace ConditionalMaster

open ResolutionCompiler

universe u v w

/-- A fully certified resolution system separates the universal geometric
input from the already verified termination compiler.  No instance of this
structure is asserted for arbitrary positive-characteristic schemes here. -/
structure System where
  Input : Type u
  P : ResolutionCompiler.Program
  initialize : Input → P.State
  resolved : P.State → Prop
  terminal_sound : ∀ s, P.terminal s → resolved s
  step_gated : ∀ {s t}, P.step s t →
    Nonempty (ResolutionCompiler.CentreGateCertificate P.State s t)

namespace System

variable (S : System)

/-- Every input of a fully certified system reaches a resolved state.  This is
the exact conditional master theorem; the outstanding mathematics is the
construction of `S` for arbitrary positive-characteristic inputs. -/
theorem every_input_resolves (x : S.Input) :
    ∃ t, ResolutionCompiler.Reaches S.P.step (S.initialize x) t ∧ S.resolved t := by
  obtain ⟨t, hreach, hterminal⟩ := S.P.terminal_reachable (S.initialize x)
  exact ⟨t, hreach, S.terminal_sound t hterminal⟩

/-- Every actual step in a certified system carries all mandatory geometric
gates. -/
theorem every_step_all_gates {s t : S.P.State} (h : S.P.step s t) :
    ∃ C : ResolutionCompiler.CentreGateCertificate S.P.State s t,
      C.actualFiniteTypeIdeal ∧ C.regularImmersion ∧ C.markedPermissible ∧
      C.passiveSafe ∧ C.boundarySNC ∧ C.allStandardCharts ∧ C.overlapGluing ∧
      C.hereditaryReentry ∧ C.nonidentity ∧ C.rankDecrease := by
  obtain ⟨C⟩ := S.step_gated h
  exact ⟨C, C.all_gates⟩

/-- A fully certified system cannot admit an infinite execution branch. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → S.P.State, ∀ n, S.P.step (f n) (f (n + 1)) :=
  S.P.no_infinite_execution

end System

/-- The universal theorem target is represented without postulating it as an
axiom: it is the proposition that a certified system exists for the chosen
input language. -/
def UniversalCertificateExists (Input : Type u) : Prop :=
  ∃ S : System, S.Input = Input

end ConditionalMaster
end PCRLean
