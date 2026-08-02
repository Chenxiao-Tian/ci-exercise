import Mathlib
import PCRLean.Termination.Generational

/-!
# Certified finite-source generation transition system

This file turns the AFPM generational rank contract into an actual Lean
transition system.  The relation contains exactly four accepted move kinds:
financed birth, source merge, cleanup, and an internal finite macro step.
Every constructor carries the strict inequality required by the corresponding
rank coordinate.  Consequently the whole transition relation is well founded.

The open geometric theorem is not hidden here: an arbitrary blowup successor
still has to be proved to enter one of these constructors.
-/

namespace PCRLean.Termination.GenerationSystem

open PCRLean.Termination.Generational

structure State where
  unusedCarrier : ℕ
  activeIdentities : ℕ
  macroRemainder : ℕ
  deriving DecidableEq, Repr

/-- The exact AFPM rank of a generation state. -/
def State.rank (s : State) : GenRank :=
  (s.unusedCarrier, (s.activeIdentities, s.macroRemainder))

/-- Accepted generation edges are oriented from the successor to its parent,
so that well-foundedness excludes an infinite forward execution. -/
inductive Step : State → State → Prop
  | financed
      {U' U A' A beta' beta : ℕ}
      (hU : U' < U) :
      Step ⟨U', A', beta'⟩ ⟨U, A, beta⟩
  | merge
      {U A' A beta' beta : ℕ}
      (hA : A' < A) :
      Step ⟨U, A', beta'⟩ ⟨U, A, beta⟩
  | cleanup
      {U A' A beta' beta : ℕ}
      (hA : A' < A) :
      Step ⟨U, A', beta'⟩ ⟨U, A, beta⟩
  | macro
      {U A beta' beta : ℕ}
      (hbeta : beta' < beta) :
      Step ⟨U, A, beta'⟩ ⟨U, A, beta⟩

/-- Every accepted generation edge lowers the lexicographic rank. -/
theorem step_rank_drop {new old : State} (h : Step new old) :
    GenLt new.rank old.rank := by
  cases h with
  | financed hU => exact financedBirth_lt hU
  | merge hA => exact sourceMerge_lt hA
  | cleanup hA => exact cleanup_lt hA
  | macro hbeta => exact macroInternal_lt hbeta

/-- The complete accepted generation relation is well founded. -/
theorem step_wellFounded : WellFounded Step := by
  apply Subrelation.wf
    (r := InvImage GenLt State.rank)
    (fun _ _ h => step_rank_drop h)
  exact InvImage.wf State.rank genLt_wellFounded

end PCRLean.Termination.GenerationSystem
