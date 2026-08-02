import Mathlib

/-!
# Fresh-birth no-go for no-recharge arguments

An age-increasing acyclic provenance chain may create a genuinely fresh
identity at every step.  No individual identity is recharged, but the process
is infinite.  This formal countermodel records why no-recharge must be paired
with a fixed finite source/carrier theorem or an independently decreasing
outer geometric rank.
-/

namespace PCRLean.NoGo.FreshBirth

/-- A transition creates the next fresh identity.  The relation is oriented
`Step child parent`. -/
def Step (child parent : ℕ) : Prop :=
  child = parent + 1

/-- The canonical infinite fresh-birth chain. -/
def chain (n : ℕ) : ℕ := n

@[simp] theorem chain_step (n : ℕ) :
    Step (chain (n + 1)) (chain n) := by
  rfl

/-- Every birth ID on the chain is globally fresh. -/
theorem birth_ids_injective : Function.Injective chain :=
  Function.injective_id

/-- Ages strictly increase along every transition. -/
theorem age_increases {child parent : ℕ} (h : Step child parent) :
    parent < child := by
  rw [h]
  exact Nat.lt_succ_self parent

/-- The fresh-birth relation is not well founded. -/
theorem not_wellFounded : ¬ WellFounded Step := by
  intro hwell
  have hempty :
      IsEmpty {f : ℕ → ℕ // ∀ n, Step (f (n + 1)) (f n)} :=
    wellFounded_iff_isEmpty_descending_chain.mp hwell
  exact hempty.false ⟨chain, chain_step⟩

/-- Consequently, the conjunction "every identity is used only once" and
"birth age strictly increases" cannot by itself be a termination theorem. -/
theorem noRecharge_and_age_do_not_imply_termination :
    Function.Injective chain ∧
    (∀ {child parent}, Step child parent → parent < child) ∧
    ¬ WellFounded Step :=
  ⟨birth_ids_injective, @age_increases, not_wellFounded⟩

end PCRLean.NoGo.FreshBirth
