import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Noetherian trace memory

The finite-dimensional Cartier ledger can be replaced by a more flexible
Noetherian module. A genuinely new trace enlarges the consumed submodule.
Noetherianity says that strict enlargement is itself a well-founded rank, so
an infinite sequence of independent births is impossible without assigning a
numerical dimension.

This is the Hilbert--Noether version of finite causal memory. It still does
not assert that every geometric descendant trace of an arbitrary singularity
lands functorially in one fixed Noetherian ancestor module.
-/

namespace PCRLean
namespace NoetherianTraceMemory

noncomputable section

universe u v

variable {R : Type u} {M : Type v}
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [IsNoetherian R M]

/-- Enlarge the consumed trace module by one trace. -/
def consume (C : Submodule R M) (x : M) : Submodule R M :=
  C ⊔ Submodule.span R {x}

/-- The old trace module is contained in the enlarged module. -/
theorem le_consume (C : Submodule R M) (x : M) : C ≤ consume C x :=
  le_sup_left

/-- The new trace is contained in the enlarged module. -/
theorem mem_consume (C : Submodule R M) (x : M) : x ∈ consume C x := by
  have hx : x ∈ Submodule.span R {x} :=
    Submodule.subset_span (by simp)
  exact (show Submodule.span R {x} ≤ consume C x from le_sup_right) hx

/-- A trace not previously generated gives a strict enlargement. -/
theorem consume_strict {C : Submodule R M} {x : M} (hx : x ∉ C) :
    C < consume C x := by
  refine lt_of_le_of_ne (le_consume C x) ?_
  intro hEq
  exact hx (hEq.symm ▸ mem_consume C x)

/-- One accepted independent-birth transition. -/
def BirthStep (C D : Submodule R M) : Prop :=
  ∃ x : M, x ∉ C ∧ D = consume C x

/-- Every accepted birth is strict enlargement of the consumed module. -/
theorem birthStep_gt {C D : Submodule R M} (h : BirthStep C D) : D > C := by
  rcases h with ⟨x, hx, rfl⟩
  exact consume_strict hx

/-- Full trace memory is terminal. -/
def Terminal (C : Submodule R M) : Prop := C = ⊤

/-- Every nonterminal submodule has an independent trace available. -/
theorem progress (C : Submodule R M) :
    ¬ Terminal C → ∃ D, BirthStep C D := by
  intro hC
  change C ≠ ⊤ at hC
  have hex : ∃ x : M, x ∉ C := by
    by_contra hnone
    apply hC
    apply le_antisymm le_top
    intro x hxTop
    by_contra hx
    exact hnone ⟨x, hx⟩
  rcases hex with ⟨x, hx⟩
  exact ⟨consume C x, x, hx, rfl⟩

/-- Strict enlargement is the native well-founded rank of a Noetherian
module. -/
def program : ResolutionCompiler.Program where
  State := Submodule R M
  Rank := Submodule R M
  step := BirthStep
  terminal := Terminal
  rank := id
  lt := (· > ·)
  wf := IsNoetherian.wf (R := R) (M := M)
    (inferInstance : IsNoetherian R M)
  decreases := birthStep_gt
  progress := progress

/-- From any initial memory, finitely many independent births generate the
whole Noetherian module. -/
theorem reaches_full_memory (C : Submodule R M) :
    ∃ D, ResolutionCompiler.Reaches BirthStep C D ∧ D = ⊤ := by
  exact program.terminal_reachable C

/-- There is no infinite sequence of genuinely independent trace births in a
fixed Noetherian ancestor module. -/
theorem no_infinite_independent_births :
    ¬ ∃ f : Nat → Submodule R M,
      ∀ n, BirthStep (f n) (f (n + 1)) :=
  program.no_infinite_execution

/-- For an endomorphism of a Noetherian trace module, sufficiently high powers
have disjoint kernel and range. This is the operator-theoretic stabilization
behind a Fitting-style recurrent chamber. -/
theorem eventually_disjoint_kernel_range (T : Module.End R M) :
    ∀ᶠ n in Filter.atTop,
      Disjoint (LinearMap.ker (T ^ n)) (LinearMap.range (T ^ n)) := by
  exact T.eventually_disjoint_ker_pow_range_pow

/-- The union of the kernel tower is eventually one actual kernel. -/
theorem eventually_kernel_tower_stabilizes (T : Module.End R M) :
    ∀ᶠ n in Filter.atTop,
      (⨆ m, LinearMap.ker (T ^ m)) = LinearMap.ker (T ^ n) := by
  exact LinearMap.eventually_iSup_ker_pow_eq T

end

end NoetherianTraceMemory
end PCRLean
