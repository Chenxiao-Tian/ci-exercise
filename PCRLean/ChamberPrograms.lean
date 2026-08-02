import Mathlib
import PCRLean.ResolutionCompiler
import PCRLean.QuadraticDebt

namespace PCRLean
namespace ChamberPrograms

open ResolutionCompiler

/-- Odd-contact cusp state: the remaining cusp depth. -/
def OddStep (n m : Nat) : Prop := 0 < n ∧ m = n - 1

def OddTerminal (n : Nat) : Prop := n = 0

/-- The odd-cusp depth program. -/
def oddProgram : ResolutionCompiler.Program where
  State := Nat
  Rank := Nat
  step := OddStep
  terminal := OddTerminal
  rank := id
  lt := (· < ·)
  wf := Nat.lt_wfRel
  decreases := by
    intro s t h
    rw [h.2]
    exact Nat.sub_one_lt h.1
  progress := by
    intro s hs
    have hspos : 0 < s := Nat.pos_of_ne_zero hs
    exact ⟨s - 1, hspos, rfl⟩

/-- Every odd cusp depth reaches zero through finitely many certified active
chart steps. -/
theorem odd_cusp_terminal_reachable (N : Nat) :
    ∃ t, ResolutionCompiler.Reaches OddStep N t ∧ t = 0 := by
  simpa [oddProgram, OddTerminal] using oddProgram.terminal_reachable N

/-- No infinite odd-cusp active-chart execution exists. -/
theorem odd_cusp_no_infinite_execution :
    ¬ ∃ f : Nat → Nat, ∀ n, OddStep (f n) (f (n + 1)) :=
  oddProgram.no_infinite_execution

/-- Tame ramified collision state: the remaining discriminant exponent. -/
def TameStep (n m : Nat) : Prop := 2 ≤ n ∧ m = n - 2

def TameTerminal (n : Nat) : Prop := n < 2

/-- The tame collision-debt program. -/
def tameProgram : ResolutionCompiler.Program where
  State := Nat
  Rank := Nat
  step := TameStep
  terminal := TameTerminal
  rank := id
  lt := (· < ·)
  wf := Nat.lt_wfRel
  decreases := by
    intro s t h
    rw [h.2]
    omega
  progress := by
    intro s hs
    have hs2 : 2 ≤ s := by omega
    exact ⟨s - 2, hs2, rfl⟩

/-- Every tame collision exponent reaches the regular parity tail in finitely
many certified collision-cylinder steps. -/
theorem tame_terminal_reachable (N : Nat) :
    ∃ t, ResolutionCompiler.Reaches TameStep N t ∧ t < 2 := by
  simpa [tameProgram, TameTerminal] using tameProgram.terminal_reachable N

/-- The Artin--Schreier collision state and active update are inherited from
the exact parameter packet. -/
abbrev ASQState := QuadraticDebt.ASQState

def ASQStep (s t : ASQState) : Prop :=
  1 ≤ s.linearDepth ∧ 2 ≤ s.tailOrder ∧ t = s.next


def ASQTerminal (s : ASQState) : Prop :=
  s.linearDepth = 0 ∨ s.tailOrder < 2

/-- The explicit Artin--Schreier collision program, ranked by `m+r`. -/
def asqProgram : ResolutionCompiler.Program where
  State := ASQState
  Rank := Nat
  step := ASQStep
  terminal := ASQTerminal
  rank := QuadraticDebt.ASQState.measure
  lt := (· < ·)
  wf := Nat.lt_wfRel
  decreases := by
    intro s t h
    rw [h.2.2]
    exact QuadraticDebt.ASQState.measureDrops s h.1 h.2.1
  progress := by
    intro s hs
    have hm : 1 ≤ s.linearDepth := by
      by_contra h
      have : s.linearDepth = 0 := by omega
      exact hs (Or.inl this)
    have hr : 2 ≤ s.tailOrder := by
      by_contra h
      exact hs (Or.inr (by omega))
    exact ⟨s.next, hm, hr, rfl⟩

/-- Every explicit ASQ collision packet reaches either zero linear depth or a
regular tail order below two in finitely many active-chart steps. -/
theorem asq_terminal_reachable (s : ASQState) :
    ∃ t, ResolutionCompiler.Reaches ASQStep s t ∧ ASQTerminal t :=
  asqProgram.terminal_reachable s

end ChamberPrograms
end PCRLean
