import Mathlib
import PCRLean.MultiHasseOnlyDescent
import PCRLean.PassiveHasseMoritaDescent
import PCRLean.GenerationalRank
import PCRLean.ResolutionCompiler

/-!
# Hasse--Morita cores and source-conservative causal descent

This module records two exact restricted exits supporting the fourth
maximum-likelihood resolution architecture.

First, the finite product Hasse packet is split into multiplication and genuine
Hasse indices also for passive block modules.  Separate stability under these
two classes implies stability under the full packet, hence Morita descent of
the passive module to one common row module.  Combined with Hasse-only ideal
descent, this constructs an active Frobenius core and a passive Morita core at
the same time.

Second, a fixed Noetherian ancestor trace module is coupled to the certified
finite-source generational rank.  Every accepted step is either a genuinely new
ancestor trace or one of the already certified source-conservative generation
moves.  The resulting lexicographic relation is well founded and compiles any
fully gated geometric realization to finite termination.

The module does not prove that arbitrary singularities admit the required
realized Frobenius frame, regular centre word, passive stability certificate,
source witness, or gated successor.  Those are the remaining geometric
interfaces.
-/

namespace PCRLean
namespace HMCSCCD

noncomputable section

universe u v w x

/-! ## Passive Hasse-only Morita descent -/

section PassiveDescent

variable {R : Type u} [CommRing R]
variable {μ : Type w}

/-- Fibrewise lift of the recursively assembled finite product packet to an
arbitrary passive row type. -/
def liftedMultiPacket
    (spec : List (Nat × R)) :
    IteratedHasseProduct.MultiPacketIndex spec →
      Module.End R ((IteratedHasseProduct.MultiIndex spec × μ) → R) :=
  PassiveHasseMoritaDescent.liftedPacket (μ := μ)
    (IteratedHasseProduct.multiPrimitivePacket (R := R) spec)

/-- Separate stability under multiplication and genuine Hasse indices gives
stability under every primitive packet generator. -/
theorem fullPacket_stable_of_split_stable
    (spec : List (Nat × R))
    (N : Submodule R
      ((IteratedHasseProduct.MultiIndex spec × μ) → R))
    (hmul : ∀ m : MultiHasseOnlyDescent.MultiplicationIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedMultiplication spec m)))
    (hhasse : ∀ d : MultiHasseOnlyDescent.HasseIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedHasse spec d))) :
    ∀ k : IteratedHasseProduct.MultiPacketIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec k) := by
  intro k
  have hsound := MultiHasseOnlyDescent.embed_classify (R := R) spec k
  cases hclass : MultiHasseOnlyDescent.classify spec k with
  | inl m =>
      have hm : MultiHasseOnlyDescent.embedMultiplication spec m = k := by
        simpa [MultiHasseOnlyDescent.embedClassified, hclass] using hsound
      rw [← hm]
      exact hmul m
  | inr d =>
      have hd : MultiHasseOnlyDescent.embedHasse spec d = k := by
        simpa [MultiHasseOnlyDescent.embedClassified, hclass] using hsound
      rw [← hd]
      exact hhasse d

/-- Passive Hasse--Morita descent with multiplication and Hasse obligations
kept logically separate. -/
theorem passive_eq_fromRowModule_of_split_stable
    (spec : List (Nat × R))
    (N : Submodule R
      ((IteratedHasseProduct.MultiIndex spec × μ) → R))
    (hmul : ∀ m : MultiHasseOnlyDescent.MultiplicationIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedMultiplication spec m)))
    (hhasse : ∀ d : MultiHasseOnlyDescent.HasseIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedHasse spec d))) :
    N = BlockMatrixStableSubmodule.fromRowModule
      (ι := IteratedHasseProduct.MultiIndex spec)
      (BlockMatrixStableSubmodule.rowModule N) := by
  exact PassiveHasseMoritaDescent.eq_fromRowModule_of_liftedPacket_stable
    (μ := μ)
    (IteratedHasseProduct.multiPrimitivePacket (R := R) spec)
    (IteratedHasseProduct.multiPrimitivePacket_generatesMatrixUnits
      (R := R) spec)
    N
    (fullPacket_stable_of_split_stable
      (R := R) (μ := μ) spec N hmul hhasse)

end PassiveDescent

/-! ## Simultaneous active and passive core construction -/

section CoreConstruction

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable {μ : Type w}
variable {spec : List (Nat × R)}

/-- On a realized finite Frobenius product frame, Hasse-only saturation of an
active ideal and split-stable passive data descend simultaneously to a base
ideal and one passive row module. -/
theorem exists_active_passive_core
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (I : Ideal A)
    (N : Submodule R
      ((IteratedHasseProduct.MultiIndex spec × μ) → R))
    (hmul : ∀ m : MultiHasseOnlyDescent.MultiplicationIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedMultiplication spec m)))
    (hhasse : ∀ d : MultiHasseOnlyDescent.HasseIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedHasse spec d))) :
    ∃ C : Ideal R, ∃ P : Submodule R (μ → R),
      F.hasseSaturation I = C.map (algebraMap R A) ∧
      N = BlockMatrixStableSubmodule.fromRowModule
        (ι := IteratedHasseProduct.MultiIndex spec) P := by
  refine ⟨F.core I, BlockMatrixStableSubmodule.rowModule N,
    F.hasseSaturation_eq_map_core I, ?_⟩
  exact passive_eq_fromRowModule_of_split_stable
    (R := R) (μ := μ) spec N hmul hhasse

section NoetherianBase

variable [IsNoetherianRing R]

/-- If the active Hasse saturation is proper, the simultaneous construction
produces a proper finitely generated Frobenius core together with the passive
Morita row core. -/
theorem exists_proper_fg_active_passive_core
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (I : Ideal A)
    (N : Submodule R
      ((IteratedHasseProduct.MultiIndex spec × μ) → R))
    (hmul : ∀ m : MultiHasseOnlyDescent.MultiplicationIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedMultiplication spec m)))
    (hhasse : ∀ d : MultiHasseOnlyDescent.HasseIndex spec,
      EndomorphismGeneration.StableUnder N
        (liftedMultiPacket (R := R) (μ := μ) spec
          (MultiHasseOnlyDescent.embedHasse spec d)))
    (hproper : F.hasseSaturation I ≠ ⊤) :
    ∃ C : Ideal R, C ≠ ⊤ ∧ C.FG ∧
      ∃ P : Submodule R (μ → R),
        F.hasseSaturation I = C.map (algebraMap R A) ∧
        N = BlockMatrixStableSubmodule.fromRowModule
          (ι := IteratedHasseProduct.MultiIndex spec) P := by
  refine ⟨F.core I,
    F.core_ne_top_of_saturation_ne_top I hproper,
    F.core_fg I,
    BlockMatrixStableSubmodule.rowModule N,
    F.hasseSaturation_eq_map_core I, ?_⟩
  exact passive_eq_fromRowModule_of_split_stable
    (R := R) (μ := μ) spec N hmul hhasse

end NoetherianBase

end CoreConstruction

/-! ## Noetherian trace plus finite-source generational rank -/

section SourceCausalRank

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- The causal rank couples a fixed-ancestor Noetherian trace memory with the
three-level finite-source generation rank. -/
abbrev CausalRank := Submodule R M × GenRank

/-- A new independent trace is primary; with unchanged trace memory, the
finite-source generation rank must decrease. -/
def CausalRankLt :
    CausalRank (R := R) (M := M) →
      CausalRank (R := R) (M := M) → Prop :=
  Prod.Lex (fun C D : Submodule R M => C > D) GenRank.Lt

/-- The combined causal rank is well founded. -/
theorem causalRankLt_wellFounded :
    WellFounded (CausalRankLt (R := R) (M := M)) := by
  exact WellFounded.prod_lex
    (IsNoetherian.wf (R := R) (M := M)
      (inferInstance : IsNoetherian R M))
    GenRank.wellFounded

/-- Exact accepted rank transitions.  A source-conservative step keeps the
ancestor trace fixed and must be one of the certified generational moves. -/
inductive CausalRankStep :
    CausalRank (R := R) (M := M) →
      CausalRank (R := R) (M := M) → Prop
  | newTrace {C D : Submodule R M} {g h : GenRank}
      (hCD : D > C) : CausalRankStep (D, g) (C, h)
  | sourceConservative {C : Submodule R M} {s t : GenState}
      (hst : GenStep s t) : CausalRankStep (C, t.rank) (C, s.rank)

/-- Every accepted causal transition decreases the combined rank. -/
theorem causalRankStep_decreases
    {child parent : CausalRank (R := R) (M := M)}
    (h : CausalRankStep child parent) :
    CausalRankLt child parent := by
  cases h with
  | newTrace hCD => exact Prod.Lex.left _ _ hCD
  | sourceConservative hst =>
      exact Prod.Lex.right _ (GenStep.decreases hst)

/-- The accepted causal transition relation is itself well founded. -/
theorem causalRankStep_wellFounded :
    WellFounded (CausalRankStep (R := R) (M := M)) := by
  exact Subrelation.wf causalRankStep_decreases causalRankLt_wellFounded

/-- A geometric program classified by actual new traces or certified
source-conservative generation moves. -/
structure CausalProgram where
  State : Type x
  step : State → State → Prop
  terminal : State → Prop
  memory : State → Submodule R M
  generation : State → GenState
  classify : ∀ {parent child}, step parent child →
    CausalRankStep
      (memory child, (generation child).rank)
      (memory parent, (generation parent).rank)
  progress : ∀ s, ¬ terminal s → ∃ t, step s t

namespace CausalProgram

variable (P : CausalProgram (R := R) (M := M))

/-- Compiled causal rank of a geometric state. -/
def compiledRank (s : P.State) : CausalRank (R := R) (M := M) :=
  (P.memory s, (P.generation s).rank)

/-- Every geometric step decreases the compiled causal rank. -/
theorem step_decreases {parent child : P.State} (h : P.step parent child) :
    CausalRankLt (P.compiledRank child) (P.compiledRank parent) := by
  exact causalRankStep_decreases (P.classify h)

/-- Compile the source-causal program into the generic verified termination
backend. -/
def toProgram : ResolutionCompiler.Program where
  State := P.State
  Rank := CausalRank (R := R) (M := M)
  step := P.step
  terminal := P.terminal
  rank := P.compiledRank
  lt := CausalRankLt (R := R) (M := M)
  wf := causalRankLt_wellFounded (R := R) (M := M)
  decreases := P.step_decreases
  progress := P.progress

/-- Every state reaches a terminal state by finitely many accepted steps. -/
theorem terminal_reachable (s : P.State) :
    ∃ t, ResolutionCompiler.Reaches P.step s t ∧ P.terminal t := by
  exact P.toProgram.terminal_reachable s

/-- No infinite execution can satisfy the fixed-trace/source-conservative
classification. -/
theorem no_infinite_execution :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) :=
  P.toProgram.no_infinite_execution

end CausalProgram

end SourceCausalRank

/-! ## Fully gated conditional resolution compiler -/

section GatedSystem

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- A fully gated geometric realization of a source-causal program. -/
structure GatedSystem
    (P : CausalProgram.{u, v, x} (R := R) (M := M))
    (Input : Type w) where
  initState : Input → P.State
  isResolved : P.State → Prop
  terminal_sound : ∀ s, P.terminal s → isResolved s
  step_gated : ∀ {parent child}, P.step parent child →
    Nonempty (ResolutionCompiler.CentreGateCertificate
      P.State parent child)

namespace GatedSystem

variable {P : CausalProgram.{u, v, x} (R := R) (M := M)}
variable {Input : Type w}
variable (S : GatedSystem (R := R) (M := M) P Input)

/-- Every input reaches a resolved state after finitely many ordinary-centre
steps, conditional on the supplied geometric system. -/
theorem every_input_resolves (input : Input) :
    ∃ finish : P.State,
      ResolutionCompiler.Reaches P.step (S.initState input) finish ∧
      S.isResolved finish := by
  obtain ⟨finish, hreach, hterminal⟩ :=
    CausalProgram.terminal_reachable P (S.initState input)
  exact ⟨finish, hreach, S.terminal_sound finish hterminal⟩

include S in
/-- Every accepted forward step exposes all mandatory actual-centre,
active/passive, boundary, chart, overlap, reentry, nonidentity, and rank gates. -/
theorem every_step_all_gates {parent child : P.State}
    (h : P.step parent child) :
    ∃ C : ResolutionCompiler.CentreGateCertificate P.State parent child,
      C.actualFiniteTypeIdeal ∧ C.regularImmersion ∧
      C.markedPermissible ∧ C.passiveSafe ∧ C.boundarySNC ∧
      C.allStandardCharts ∧ C.overlapGluing ∧ C.hereditaryReentry ∧
      C.nonidentity ∧ C.rankDecrease := by
  obtain ⟨C⟩ := S.step_gated h
  exact ⟨C, C.all_gates⟩

/-- The gated source-causal system has no infinite execution branch. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → P.State, ∀ n, P.step (f n) (f (n + 1)) :=
  CausalProgram.no_infinite_execution P

end GatedSystem

end GatedSystem

end

end HMCSCCD
end PCRLean
