import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Cartier finite memory and independent-birth descent

This file isolates the algebraic core of a history-inspired termination idea.
A future trace is represented by a vector in one fixed finite-dimensional
operator module.  When a genuinely new trace appears, the consumed subspace is
enlarged by that vector.  Its codimension debt drops exactly by one.  Repeated
operator images cannot remain algebraically independent forever, and every
endomorphism satisfies a monic polynomial recurrence by Cayley--Hamilton.

The file does not assert that arbitrary geometric transforms in positive
characteristic have already been embedded into such a fixed module.  That is
the geometric realization problem to be proved separately.
-/

namespace PCRLean
namespace CartierFiniteMemory

noncomputable section

universe u v

variable {K : Type u} {V : Type v}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Enlarge the consumed memory by one newly observed trace. -/
def consume (C : Submodule K V) (x : V) : Submodule K V :=
  C ⊔ Submodule.span K {x}

/-- The old consumed memory is contained in the enlarged memory. -/
theorem le_consume (C : Submodule K V) (x : V) : C ≤ consume C x := by
  exact le_sup_left

/-- The newly consumed trace belongs to the enlarged memory. -/
theorem mem_consume (C : Submodule K V) (x : V) : x ∈ consume C x := by
  exact le_sup_right (Submodule.subset_span (by simp))

/-- A genuinely new trace strictly enlarges the consumed subspace. -/
theorem consume_strict {C : Submodule K V} {x : V} (hx : x ∉ C) :
    C < consume C x := by
  refine lt_of_le_of_ne (le_consume C x) ?_
  intro hEq
  apply hx
  exact hEq.symm ▸ mem_consume C x

/-- Consuming a genuinely new trace increases the consumed dimension by one. -/
theorem finrank_consume {C : Submodule K V} {x : V} (hx : x ∉ C) :
    Module.finrank K (consume C x) = Module.finrank K C + 1 := by
  simpa [consume] using
    (Submodule.finrank_sup_span_singleton (K := K) (p := C) (v := x) hx)

/-- Remaining finite-memory debt. -/
def debt (C : Submodule K V) : Nat :=
  Module.finrank K V - Module.finrank K C

/-- A genuinely new trace pays exactly one unit of codimension debt. -/
theorem debt_consume_add_one {C : Submodule K V} {x : V} (hx : x ∉ C) :
    debt (consume C x) + 1 = debt C := by
  have hle : Module.finrank K (consume C x) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  rw [finrank_consume hx] at hle
  unfold debt
  rw [finrank_consume hx]
  omega

/-- In particular, every independent birth strictly decreases the debt. -/
theorem debt_consume_lt {C : Submodule K V} {x : V} (hx : x ∉ C) :
    debt (consume C x) < debt C := by
  have h := debt_consume_add_one hx
  omega

/-- One accepted independent-birth step. -/
def BirthStep (C D : Submodule K V) : Prop :=
  ∃ x : V, x ∉ C ∧ D = consume C x

/-- Every accepted independent birth strictly lowers finite-memory debt. -/
theorem birthStep_decreases {C D : Submodule K V} (h : BirthStep C D) :
    debt D < debt C := by
  rcases h with ⟨x, hx, rfl⟩
  exact debt_consume_lt hx

/-- Full memory is the terminal state. -/
def Terminal (C : Submodule K V) : Prop := C = ⊤

/-- Every nonterminal memory admits a genuinely new vector. -/
theorem progress (C : Submodule K V) :
    ¬ Terminal C → ∃ D, BirthStep C D := by
  intro hC
  change C ≠ ⊤ at hC
  have hex : ∃ x : V, x ∉ C := by
    by_contra hnone
    apply hC
    apply le_antisymm le_top
    intro x hxTop
    by_contra hx
    exact hnone ⟨x, hx⟩
  rcases hex with ⟨x, hx⟩
  exact ⟨consume C x, x, hx, rfl⟩

/-- The finite-memory independent-birth program. -/
def program : ResolutionCompiler.Program where
  State := Submodule K V
  Rank := Nat
  step := BirthStep
  terminal := Terminal
  rank := debt
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  decreases := birthStep_decreases
  progress := progress

/-- Starting from any consumed subspace, finitely many genuinely independent
births saturate the ambient finite memory. -/
theorem reaches_full_memory (C : Submodule K V) :
    ∃ D, ResolutionCompiler.Reaches BirthStep C D ∧ D = ⊤ := by
  exact program.terminal_reachable C

/-- There is no infinite stream of genuinely independent births in one fixed
finite-dimensional memory module. -/
theorem no_infinite_independent_births :
    ¬ ∃ f : Nat → Submodule K V,
      ∀ n, BirthStep (f n) (f (n + 1)) :=
  program.no_infinite_execution

/-- Every endomorphism of finite memory satisfies a monic polynomial
recurrence.  When the endomorphism is a Cartier/Frobenius trace operator, this
is the finite additive-recurrence certificate. -/
theorem endomorphism_has_monic_recurrence (T : Module.End K V) :
    ∃ p : Polynomial K, p.Monic ∧ Polynomial.aeval T p = 0 := by
  exact LinearMap.exists_monic_and_aeval_eq_zero K T

/-- The monic recurrence annihilates every chosen trace vector. -/
theorem trace_has_monic_recurrence (T : Module.End K V) (x : V) :
    ∃ p : Polynomial K, p.Monic ∧ Polynomial.aeval T p x = 0 := by
  rcases endomorphism_has_monic_recurrence T with ⟨p, hp, hzero⟩
  refine ⟨p, hp, ?_⟩
  have happly := congrArg (fun S : Module.End K V => S x) hzero
  simpa using happly

end

end CartierFiniteMemory
end PCRLean
