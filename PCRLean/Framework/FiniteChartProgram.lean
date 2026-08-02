import Mathlib

/-!
# Finite all-chart resolution programs

`CertifiedProgram` proves existence of one terminating path.  Resolution by a
blowup, however, must control every standard chart.  This file introduces a
finite-branching certificate whose successor list is the complete chart list.
A strict rank on every listed child, nonempty successor lists at nonterminal
states, terminal soundness, and edge legality produce a finite all-chart
resolution tree.

The theorem is a logical compiler.  A geometric front end must still construct
the complete successor lists and prove their legality and strict descent.
-/

namespace PCRLean.Framework

/-- A finite all-chart program with one legality predicate for each edge. -/
structure FiniteChartProgram where
  State : Type*
  children : State → List State
  rank : State → ℕ
  terminal : State → Prop
  resolved : State → Prop
  legal : State → State → Prop
  child_decreases : ∀ {child parent}, child ∈ children parent →
    rank child < rank parent
  child_legal : ∀ {child parent}, child ∈ children parent →
    legal child parent
  progress : ∀ parent, ¬ terminal parent → (children parent).Nonempty
  terminal_resolved : ∀ {state}, terminal state → resolved state

namespace FiniteChartProgram

variable (P : FiniteChartProgram)

/-- The complete child relation. -/
def Step (child parent : P.State) : Prop :=
  child ∈ P.children parent

/-- The complete child relation is well founded. -/
theorem step_wellFounded : WellFounded P.Step := by
  have hNat : WellFounded ((· < ·) : ℕ → ℕ → Prop) := Nat.lt_wfRel.wf
  exact (hNat.onFun (f := P.rank)).mono
    (fun _ _ hchild => P.child_decreases hchild)

/-- A proof object that every branch below a state is finite, every internal
node has at least one child, every listed edge is legal, and every leaf is a
resolved terminal state. -/
inductive ResolvesAll : P.State → Prop
  | terminal {state} : P.terminal state → ResolvesAll state
  | branch {state} :
      ¬ P.terminal state →
      (P.children state).Nonempty →
      (∀ child, child ∈ P.children state → P.legal child state) →
      (∀ child, child ∈ P.children state → ResolvesAll child) →
      ResolvesAll state

/-- Every state of a finite chart program has a complete finite resolution
tree. -/
theorem resolvesAll (start : P.State) : P.ResolvesAll start := by
  induction start using P.step_wellFounded.induction with
  | h state ih =>
      by_cases hterminal : P.terminal state
      · exact ResolvesAll.terminal hterminal
      · exact ResolvesAll.branch hterminal (P.progress state hterminal)
          (fun child hmem => P.child_legal hmem)
          (fun child hmem => ih child hmem)

/-- Every leaf occurring in a certified all-chart tree is terminal.  This
predicate is useful when extracting a paper-level terminal statement. -/
def IsLeaf (state : P.State) : Prop :=
  P.children state = []

/-- A nonterminal state cannot be a leaf. -/
theorem terminal_of_leaf {state : P.State} (hleaf : P.IsLeaf state) :
    P.terminal state := by
  by_contra hterminal
  obtain ⟨child, hchild⟩ := P.progress state hterminal
  rw [hleaf] at hchild
  simpa using hchild

/-- Therefore every leaf is resolved. -/
theorem resolved_of_leaf {state : P.State} (hleaf : P.IsLeaf state) :
    P.resolved state :=
  P.terminal_resolved (P.terminal_of_leaf hleaf)

/-- Every listed chart transition satisfies the declared legality predicate. -/
theorem legal_of_step {child parent : P.State} (h : P.Step child parent) :
    P.legal child parent :=
  P.child_legal h

end FiniteChartProgram

end PCRLean.Framework
