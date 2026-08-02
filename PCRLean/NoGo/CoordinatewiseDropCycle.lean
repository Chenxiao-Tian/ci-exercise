import Mathlib

/-!
# Coordinatewise-drop cycle

A transition system can have the property that on every edge some natural
coordinate decreases while another coordinate resets.  This does not yield a
single well-founded global rank.  The two-state cycle below is the smallest
formal countermodel to that inference.
-/

namespace PCRLean.NoGo.CoordinatewiseDropCycle

inductive State where
  | a
  | b
  deriving DecidableEq, Repr

/-- The two-edge directed cycle, oriented `Step child parent`. -/
inductive Step : State → State → Prop
  | ab : Step .b .a
  | ba : Step .a .b

/-- First local coordinate. -/
def first : State → ℕ
  | .a => 0
  | .b => 1

/-- Second local coordinate. -/
def second : State → ℕ
  | .a => 1
  | .b => 0

/-- Every edge lowers at least one of the two displayed coordinates. -/
theorem some_coordinate_drops {child parent : State} (h : Step child parent) :
    first child < first parent ∨ second child < second parent := by
  cases h <;> simp [first, second]

/-- Toggle between the two states. -/
def toggle : State → State
  | .a => .b
  | .b => .a

@[simp] theorem step_toggle (s : State) : Step (toggle s) s := by
  cases s <;> constructor

/-- An explicit infinite branch. -/
def chain : ℕ → State
  | 0 => .a
  | n + 1 => toggle (chain n)

@[simp] theorem chain_step (n : ℕ) :
    Step (chain (n + 1)) (chain n) :=
  step_toggle _

/-- The relation is not well founded despite coordinatewise local drops. -/
theorem not_wellFounded : ¬ WellFounded Step := by
  intro hwell
  have hempty :
      IsEmpty {f : ℕ → State // ∀ n, Step (f (n + 1)) (f n)} :=
    wellFounded_iff_isEmpty_descending_chain.mp hwell
  exact hempty.false ⟨chain, chain_step⟩

/-- Formal rejection of the implication "some coordinate drops on every edge,
therefore the process terminates". -/
theorem local_coordinate_drop_is_insufficient :
    (∀ {child parent}, Step child parent →
      first child < first parent ∨ second child < second parent) ∧
    ¬ WellFounded Step :=
  ⟨@some_coordinate_drops, not_wellFounded⟩

end PCRLean.NoGo.CoordinatewiseDropCycle
