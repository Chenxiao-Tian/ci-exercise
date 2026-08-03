import Std.Tactic

/-!
# Final positive-characteristic resolution proof blueprint

This file verifies the logical sufficiency of the five-paper proof architecture
registered as `PCR-FPE-001 / FCRES-TOP`.

It does **not** assume the open mathematical bridge theorems as Lean axioms.
Instead, each paper exports a typed certificate through fields of `Pipeline`.
The main theorem below proves that any implementation of all five interfaces
produces a finite global ordinary-blowup resolution bundle.

Consequently, a missing theorem remains a visible uninhabited field of the
pipeline rather than a hidden axiom, `sorry`, or semantic weakening.
-/

namespace PCRLean
namespace Spec
namespace FinalResolutionBlueprint

universe u

/-- Abstract semantic language shared by the five papers. -/
structure Language where
  Input : Type u
  State : Type u
  Packet : Type u
  Centre : Type u
  Obstruction : Type u
  GlobalProgram : Type u

  initial : Input → State
  stateLt : State → State → Prop

  packetFinite : Packet → Prop
  packetIntrinsic : State → Packet → Prop
  packetPresentationIndependent : Packet → Prop
  packetBaseChangeCompatible : Packet → Prop
  packetPreservesMarkedSemantics : State → Packet → Prop
  packetPreservesOwners : State → Packet → Prop
  packetPreservesHistory : State → Packet → Prop

  centreActual : Centre → Prop
  centreFiniteType : Centre → Prop
  centreRegular : Centre → Prop
  centreNonidentity : Centre → Prop
  centreInSingularLocus : State → Centre → Prop
  centreActiveLegal : State → Centre → Prop
  centrePassiveSafe : State → Centre → Prop
  centreBoundarySNC : State → Centre → Prop
  centreSymmetryCompatible : State → Centre → Prop

  obstructionFiniteType : Obstruction → Prop
  obstructionIntrinsic : State → Obstruction → Prop
  obstructionClassified : Obstruction → Prop
  obstructionSourceTracked : State → Obstruction → Prop

  ordinaryBlowup : State → Centre → State → Prop
  allChartsControlled : State → Centre → State → Prop
  overlapsGlue : State → Centre → State → Prop
  packetTransported : State → State → Prop
  ownersTransported : State → State → Prop
  boundaryTransported : State → State → Prop
  historyTransported : State → State → Prop
  noReset : State → State → Prop

  terminal : State → Prop
  terminalRegular : State → Prop
  terminalBoundarySNC : State → Prop

  globalFinite : GlobalProgram → Prop
  globalOrdinaryBlowups : GlobalProgram → Prop
  globalActualRegularCentres : GlobalProgram → Prop
  globalSmoothFunctorial : GlobalProgram → Prop
  globalEtaleFunctorial : GlobalProgram → Prop
  globalPerfectFieldFunctorial : GlobalProgram → Prop
  principalizes : Input → GlobalProgram → Prop
  embeddedResolves : Input → GlobalProgram → Prop
  nonembeddedResolves : Input → GlobalProgram → Prop

variable (L : Language)

/-- Paper I export: a finite intrinsic normalized packet preserving semantics. -/
structure PaperIResult (s : L.State) where
  packet : L.Packet
  finite : L.packetFinite packet
  intrinsic : L.packetIntrinsic s packet
  presentationIndependent : L.packetPresentationIndependent packet
  baseChangeCompatible : L.packetBaseChangeCompatible packet
  markedSemantics : L.packetPreservesMarkedSemantics s packet
  owners : L.packetPreservesOwners s packet
  history : L.packetPreservesHistory s packet

/-- Paper II centre branch: one actual jointly legal geometric action. -/
structure CentreResult (s : L.State) where
  centre : L.Centre
  actual : L.centreActual centre
  finiteType : L.centreFiniteType centre
  regular : L.centreRegular centre
  nonidentity : L.centreNonidentity centre
  singularContained : L.centreInSingularLocus s centre
  activeLegal : L.centreActiveLegal s centre
  passiveSafe : L.centrePassiveSafe s centre
  boundarySNC : L.centreBoundarySNC s centre
  symmetryCompatible : L.centreSymmetryCompatible s centre

/-- Paper II obstruction branch: finite intrinsic data requiring Paper IV escape. -/
structure ObstructionResult (s : L.State) where
  obstruction : L.Obstruction
  finiteType : L.obstructionFiniteType obstruction
  intrinsic : L.obstructionIntrinsic s obstruction
  classified : L.obstructionClassified obstruction
  sourceTracked : L.obstructionSourceTracked s obstruction

/-- Paper III export: one complete hereditary ordinary-blowup transition. -/
structure StepResult (parent : L.State) where
  child : L.State
  centre : L.Centre
  ordinary : L.ordinaryBlowup parent centre child
  allCharts : L.allChartsControlled parent centre child
  overlap : L.overlapsGlue parent centre child
  packet : L.packetTransported parent child
  owners : L.ownersTransported parent child
  boundary : L.boundaryTransported parent child
  history : L.historyTransported parent child
  noReset : L.noReset parent child
  decreases : L.stateLt child parent

/-- Terminal local state exported by Papers III or IV. -/
structure TerminalResult (s : L.State) where
  terminal : L.terminal s
  regular : L.terminalRegular s
  boundarySNC : L.terminalBoundarySNC s

/-- A finite local resolution program certified step by step. -/
inductive LocalProgram : L.State → Type u
  | done {s : L.State} (terminal : TerminalResult L s) : LocalProgram s
  | step {s : L.State} (move : StepResult L s)
      (rest : LocalProgram move.child) : LocalProgram s

/-- Paper V export: a finite global ordinary-blowup program with all final consequences. -/
structure FinalResolutionBundle (input : L.Input) where
  program : L.GlobalProgram
  finite : L.globalFinite program
  ordinaryBlowups : L.globalOrdinaryBlowups program
  actualRegularCentres : L.globalActualRegularCentres program
  smoothFunctorial : L.globalSmoothFunctorial program
  etaleFunctorial : L.globalEtaleFunctorial program
  perfectFieldFunctorial : L.globalPerfectFieldFunctorial program
  principalization : L.principalizes input program
  embeddedResolution : L.embeddedResolves input program
  nonembeddedResolution : L.nonembeddedResolves input program

/-- The five paper APIs.  Open mathematical theorems occur only as fields of
this structure; no project-specific axiom is declared. -/
structure Pipeline where
  /-- `PCR-P1-MAIN-045`: finite normalized packet entry. -/
  paperI : ∀ s : L.State, PaperIResult L s

  /-- `PCR-P2-MAIN-045`: legal centre or classified obstruction. -/
  paperII : ∀ s : L.State, PaperIResult L s →
    CentreResult L s ⊕ ObstructionResult L s

  /-- `PCR-P3-MAIN-045`: hereditary ordinary-blowup step. -/
  paperIII : ∀ s : L.State, PaperIResult L s → CentreResult L s →
    StepResult L s

  /-- `PCR-P4-MAIN-045`: every classified obstruction terminates or escapes
  by a strictly decreasing certified step. -/
  paperIV : ∀ s : L.State, PaperIResult L s → ObstructionResult L s →
    TerminalResult L s ⊕ StepResult L s

  /-- Paper IV global well-foundedness export. -/
  stateWellFounded : WellFounded L.stateLt

  /-- `PCR-P5-MAIN-045`: globalization and the three resolution compilers. -/
  paperV : ∀ input : L.Input,
    LocalProgram L (L.initial input) → FinalResolutionBundle L input

namespace Pipeline

variable (P : Pipeline L)

/-- The first four paper exports give progress or terminality at every state. -/
def progress (s : L.State) : TerminalResult L s ⊕ StepResult L s :=
  let packet := P.paperI s
  match P.paperII s packet with
  | Sum.inl centre => Sum.inr (P.paperIII s packet centre)
  | Sum.inr obstruction => P.paperIV s packet obstruction

/-- Well-founded progress compiles to a finite local program. -/
theorem existsLocalProgram (s : L.State) :
    Nonempty (LocalProgram L s) :=
  P.stateWellFounded.induction s fun s ih => by
    cases h : P.progress s with
    | inl terminal =>
        exact ⟨LocalProgram.done terminal⟩
    | inr move =>
        exact (ih move.child move.decreases).map fun rest =>
          LocalProgram.step move rest

/-- The five-paper architecture strictly implies the final resolution bundle. -/
theorem pipeline_implies_final_resolution (input : L.Input) :
    Nonempty (FinalResolutionBundle L input) :=
  (P.existsLocalProgram (L.initial input)).map (P.paperV input)

/-- Strong embedded resolution is a formal consequence of the bundle. -/
theorem pipeline_implies_embedded_resolution (input : L.Input) :
    ∃ program : L.GlobalProgram,
      L.globalFinite program ∧
      L.globalOrdinaryBlowups program ∧
      L.globalActualRegularCentres program ∧
      L.embeddedResolves input program := by
  rcases P.pipeline_implies_final_resolution input with ⟨bundle⟩
  exact ⟨bundle.program, bundle.finite, bundle.ordinaryBlowups,
    bundle.actualRegularCentres, bundle.embeddedResolution⟩

/-- Principalization is a formal consequence of the same bundle. -/
theorem pipeline_implies_principalization (input : L.Input) :
    ∃ program : L.GlobalProgram,
      L.globalFinite program ∧ L.principalizes input program := by
  rcases P.pipeline_implies_final_resolution input with ⟨bundle⟩
  exact ⟨bundle.program, bundle.finite, bundle.principalization⟩

/-- Nonembedded resolution is a formal consequence of the same bundle. -/
theorem pipeline_implies_nonembedded_resolution (input : L.Input) :
    ∃ program : L.GlobalProgram,
      L.globalFinite program ∧ L.nonembeddedResolves input program := by
  rcases P.pipeline_implies_final_resolution input with ⟨bundle⟩
  exact ⟨bundle.program, bundle.finite, bundle.nonembeddedResolution⟩

end Pipeline

end FinalResolutionBlueprint
end Spec
end PCRLean
