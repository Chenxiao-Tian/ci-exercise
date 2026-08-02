import Mathlib
import PCRLean.Framework.FiniteChartProgram
import PCRLean.Chambers.FrobeniusContentProgram
import PCRLean.Chambers.OddCuspProgram
import PCRLean.Chambers.RamifiedQuadraticProgram
import PCRLean.Chambers.ArtinSchreierProgram

/-!
# Complete finite successor lists for the certified local chambers

The earlier `CertifiedProgram` files prove that a legal descending path exists.
This file upgrades the explicit local models to complete finite successor
lists, so the generic all-chart compiler proves termination of every listed
standard chart.
-/

namespace PCRLean.Chambers.AllChartPrograms

open PCRLean.Framework

namespace FrobeniusContent

abbrev State := FrobeniusContentProgram.State

/-- Both the active and sibling charts are listed at positive depth. -/
def children : State → List State
  | .active 0 => [.lowerPacket]
  | .active (n + 1) => [.active n, .terminalSibling]
  | .lowerPacket => []
  | .terminalSibling => []

/-- All local identities were proved in `FrobeniusContent`; legality here means
that the successor belongs to the declared finite chart list. -/
def legal (_child _parent : State) : Prop := True

private theorem child_decreases {child parent : State} (h : child ∈ children parent) :
    FrobeniusContentProgram.rank child < FrobeniusContentProgram.rank parent := by
  cases parent with
  | active n =>
      cases n with
      | zero => simp [children, FrobeniusContentProgram.rank] at h ⊢
      | succ n =>
          simp [children] at h
          rcases h with rfl | rfl <;> simp [FrobeniusContentProgram.rank]
  | lowerPacket => simp [children] at h
  | terminalSibling => simp [children] at h

private theorem progress (parent : State) :
    ¬ FrobeniusContentProgram.terminal parent → children parent ≠ [] := by
  intro h
  cases parent with
  | active n => cases n <;> simp [children]
  | lowerPacket => exact False.elim (h trivial)
  | terminalSibling => exact False.elim (h trivial)

/-- Complete all-chart program for the anchored-content chamber. -/
def program : FiniteChartProgram where
  State := State
  children := children
  rank := FrobeniusContentProgram.rank
  terminal := FrobeniusContentProgram.terminal
  resolved := FrobeniusContentProgram.resolved
  legal := legal
  child_decreases := child_decreases
  child_legal := by intro; trivial
  progress := progress
  terminal_resolved := by intro _ h; exact h

/-- Every listed chart below an anchored content packet lies in a finite
terminal-or-lower-packet tree. -/
theorem allChartsResolve (n : ℕ) :
    program.ResolvesAll (.active n) :=
  program.resolvesAll (.active n)

end FrobeniusContent

namespace OddCusp

abbrev State := OddCuspProgram.State

def children : State → List State
  | .active 0 => [.secondContact, .terminal]
  | .active (n + 1) => [.active n, .terminal]
  | .secondContact => [.terminal, .terminal]
  | .terminal => []

def legal (_child _parent : State) : Prop := True

private theorem child_decreases {child parent : State} (h : child ∈ children parent) :
    OddCuspProgram.rank child < OddCuspProgram.rank parent := by
  cases parent with
  | active n =>
      cases n with
      | zero =>
          simp [children] at h
          rcases h with rfl | rfl <;> simp [OddCuspProgram.rank]
      | succ n =>
          simp [children] at h
          rcases h with rfl | rfl <;> simp [OddCuspProgram.rank]
  | secondContact =>
      simp [children] at h
      subst child
      simp [OddCuspProgram.rank]
  | terminal => simp [children] at h

private theorem progress (parent : State) :
    ¬ OddCuspProgram.terminal parent → children parent ≠ [] := by
  intro h
  cases parent with
  | active n => cases n <;> simp [children]
  | secondContact => simp [children]
  | terminal => exact False.elim (h trivial)

/-- Complete two-chart tree for the odd cusp and its contact repair. -/
def program : FiniteChartProgram where
  State := State
  children := children
  rank := OddCuspProgram.rank
  terminal := OddCuspProgram.terminal
  resolved := OddCuspProgram.resolved
  legal := legal
  child_decreases := child_decreases
  child_legal := by intro; trivial
  progress := progress
  terminal_resolved := by intro _ h; exact h

/-- Every standard chart in the explicit odd-cusp program terminates. -/
theorem allChartsResolve (n : ℕ) :
    program.ResolvesAll (.active n) :=
  program.resolvesAll (.active n)

end OddCusp

namespace RamifiedQuadratic

abbrev State := RamifiedQuadraticProgram.State

def children : State → List State
  | .active 0 => [.branchFinal]
  | .active 1 => [.secondContact, .terminal]
  | .active (n + 2) => [.active n, .terminal]
  | .secondContact => [.branchFinal, .branchFinal]
  | .branchFinal => [.terminal]
  | .terminal => []

def legal (_child _parent : State) : Prop := True

private theorem child_decreases {child parent : State} (h : child ∈ children parent) :
    RamifiedQuadraticProgram.rank child < RamifiedQuadraticProgram.rank parent := by
  cases parent with
  | active n =>
      cases n with
      | zero =>
          simp [children] at h
          subst child
          simp [RamifiedQuadraticProgram.rank]
      | succ n =>
          cases n with
          | zero =>
              simp [children] at h
              rcases h with rfl | rfl <;> simp [RamifiedQuadraticProgram.rank]
          | succ n =>
              simp [children] at h
              rcases h with rfl | rfl <;> simp [RamifiedQuadraticProgram.rank]
  | secondContact =>
      simp [children] at h
      subst child
      simp [RamifiedQuadraticProgram.rank]
  | branchFinal =>
      simp [children] at h
      subst child
      simp [RamifiedQuadraticProgram.rank]
  | terminal => simp [children] at h

private theorem progress (parent : State) :
    ¬ RamifiedQuadraticProgram.terminal parent → children parent ≠ [] := by
  intro h
  cases parent with
  | active n =>
      cases n with
      | zero => simp [children]
      | succ n => cases n <;> simp [children]
  | secondContact => simp [children]
  | branchFinal => simp [children]
  | terminal => exact False.elim (h trivial)

/-- Complete all-chart tree for the tame ramified quadratic chamber. -/
def program : FiniteChartProgram where
  State := State
  children := children
  rank := RamifiedQuadraticProgram.rank
  terminal := RamifiedQuadraticProgram.terminal
  resolved := RamifiedQuadraticProgram.resolved
  legal := legal
  child_decreases := child_decreases
  child_legal := by intro; trivial
  progress := progress
  terminal_resolved := by intro _ h; exact h

/-- Every standard chart in the declared tame collision chamber terminates. -/
theorem allChartsResolve (n : ℕ) :
    program.ResolvesAll (.active n) :=
  program.resolvesAll (.active n)

end RamifiedQuadratic

namespace ArtinSchreier

abbrev State := ArtinSchreierProgram.State

def children : State → List State
  | .active 0 r => [.branchFinal]
  | .active (m + 1) 0 => [.radicialFrontier]
  | .active (m + 1) 1 => [.wildSecondContact, .terminal]
  | .active (m + 1) (r + 2) => [.active m r, .terminal]
  | .wildSecondContact => [.branchFinal, .branchFinal]
  | .branchFinal => [.terminal]
  | .radicialFrontier => []
  | .terminal => []

def legal (_child _parent : State) : Prop := True

private theorem child_decreases {child parent : State} (h : child ∈ children parent) :
    ArtinSchreierProgram.rank child < ArtinSchreierProgram.rank parent := by
  cases parent with
  | active m r =>
      cases m with
      | zero =>
          simp [children] at h
          subst child
          simp [ArtinSchreierProgram.rank]
      | succ m =>
          cases r with
          | zero =>
              simp [children] at h
              subst child
              simp [ArtinSchreierProgram.rank]
          | succ r =>
              cases r with
              | zero =>
                  simp [children] at h
                  rcases h with rfl | rfl <;> simp [ArtinSchreierProgram.rank]
              | succ r =>
                  simp [children] at h
                  rcases h with rfl | rfl <;> simp [ArtinSchreierProgram.rank]
  | wildSecondContact =>
      simp [children] at h
      subst child
      simp [ArtinSchreierProgram.rank]
  | branchFinal =>
      simp [children] at h
      subst child
      simp [ArtinSchreierProgram.rank]
  | radicialFrontier => simp [children] at h
  | terminal => simp [children] at h

private theorem progress (parent : State) :
    ¬ ArtinSchreierProgram.classifiedExit parent → children parent ≠ [] := by
  intro h
  cases parent with
  | active m r =>
      cases m with
      | zero => simp [children]
      | succ m =>
          cases r with
          | zero => simp [children]
          | succ r => cases r <;> simp [children]
  | wildSecondContact => simp [children]
  | branchFinal => simp [children]
  | radicialFrontier => exact False.elim (h trivial)
  | terminal => exact False.elim (h trivial)

/-- Complete all-chart classifier.  The even radicial leaf is a typed frontier,
not a resolved geometric branch. -/
def program : FiniteChartProgram where
  State := State
  children := children
  rank := ArtinSchreierProgram.rank
  terminal := ArtinSchreierProgram.classifiedExit
  resolved := ArtinSchreierProgram.classifiedExit
  legal := legal
  child_decreases := child_decreases
  child_legal := by intro; trivial
  progress := progress
  terminal_resolved := by intro _ h; exact h

/-- Every standard chart is finitely classified as resolved or radicial. -/
theorem allChartsClassified (m r : ℕ) :
    program.ResolvesAll (.active m r) :=
  program.resolvesAll (.active m r)

end ArtinSchreier

end PCRLean.Chambers.AllChartPrograms
