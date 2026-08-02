import Mathlib
import PCRLean.GenerationalRank

namespace PCRLean
namespace ResolutionCompiler

universe u v

/-- Finite reachability by certified forward steps. -/
inductive Reaches {State : Type u} (step : State → State → Prop) :
    State → State → Prop
  | refl (s : State) : Reaches step s s
  | cons {s t u : State} (hst : step s t) (htu : Reaches step t u) :
      Reaches step s u

/-- Reachability is transitive. -/
theorem Reaches.trans {State : Type u} {step : State → State → Prop}
    {a b c : State} (hab : Reaches step a b) (hbc : Reaches step b c) :
    Reaches step a c := by
  induction hab with
  | refl _ => exact hbc
  | cons hst _ ih => exact Reaches.cons hst (ih hbc)

/-- The abstract data required by the termination backend. Geometry supplies
`step`, `terminal`, and the strict rank theorem; the compiler supplies finite
termination. -/
structure Program where
  State : Type u
  Rank : Type v
  step : State → State → Prop
  terminal : State → Prop
  rank : State → Rank
  lt : Rank → Rank → Prop
  wf : WellFounded lt
  decreases : ∀ {s t}, step s t → lt (rank t) (rank s)
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace Program

variable (P : Program)

/-- The state relation induced by the program rank. -/
def stateLt (t s : P.State) : Prop := P.lt (P.rank t) (P.rank s)

/-- The induced state relation is well founded. -/
theorem stateLt_wf : WellFounded P.stateLt := by
  exact InvImage.wf P.rank P.wf

/-- Every state has a terminal descendant reached by finitely many certified
steps. This theorem is the kernel-checked abstract termination compiler. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, Reaches P.step s t ∧ P.terminal t := by
  induction s using P.stateLt_wf.induction with
  | h s ih =>
      by_cases hs : P.terminal s
      · exact ⟨s, Reaches.refl s, hs⟩
      · obtain ⟨t, hst⟩ := P.progress s hs
        have hlt : P.stateLt t s := P.decreases hst
        obtain ⟨u, htu, hu⟩ := ih t hlt
        exact ⟨u, Reaches.cons hst htu, hu⟩

/-- An infinite certified execution is impossible. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending P.wf (fun n => P.rank (f n))
    (fun n => P.decreases (hf n))

end Program

/-- The mandatory geometric gates for one ordinary-centre action. This is a
semantic certificate record, not an assumption that such a certificate exists
for arbitrary positive-characteristic inputs. -/
structure CentreGateCertificate (State : Type u) (s t : State) : Type where
  actualFiniteTypeIdeal : Prop
  actualFiniteTypeIdeal_proof : actualFiniteTypeIdeal
  regularImmersion : Prop
  regularImmersion_proof : regularImmersion
  markedPermissible : Prop
  markedPermissible_proof : markedPermissible
  passiveSafe : Prop
  passiveSafe_proof : passiveSafe
  boundarySNC : Prop
  boundarySNC_proof : boundarySNC
  allStandardCharts : Prop
  allStandardCharts_proof : allStandardCharts
  overlapGluing : Prop
  overlapGluing_proof : overlapGluing
  hereditaryReentry : Prop
  hereditaryReentry_proof : hereditaryReentry
  nonidentity : Prop
  nonidentity_proof : nonidentity
  rankDecrease : Prop
  rankDecrease_proof : rankDecrease

/-- A certified centre action automatically exposes every mandatory gate. -/
theorem CentreGateCertificate.all_gates
    {State : Type u} {s t : State} (C : CentreGateCertificate State s t) :
    C.actualFiniteTypeIdeal ∧ C.regularImmersion ∧ C.markedPermissible ∧
    C.passiveSafe ∧ C.boundarySNC ∧ C.allStandardCharts ∧ C.overlapGluing ∧
    C.hereditaryReentry ∧ C.nonidentity ∧ C.rankDecrease := by
  exact ⟨C.actualFiniteTypeIdeal_proof, C.regularImmersion_proof,
    C.markedPermissible_proof, C.passiveSafe_proof, C.boundarySNC_proof,
    C.allStandardCharts_proof, C.overlapGluing_proof,
    C.hereditaryReentry_proof, C.nonidentity_proof, C.rankDecrease_proof⟩

end ResolutionCompiler
end PCRLean
