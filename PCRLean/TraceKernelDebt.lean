import Mathlib
import PCRLean.ResolutionCompiler

/-!
# Trace growth and persistent-kernel debt

A differential/Hasse--Cartier packet is represented by a subspace of the dual
of a finite-dimensional direction space. Its common zero set is the dual
coannihilator. Enlarging the trace space shrinks the persistent kernel, and
adjoining one genuinely independent trace lowers the kernel dimension by
exactly one.

This is the finite-dimensional conservation law needed by the causal-birth
program: a new independent trace cannot be created for free. The geometric
realization problem is to prove that every jump-capable birth either supplies
such an independent trace in one fixed ancestor bundle or pays a separate
local rank.
-/

namespace PCRLean
namespace TraceKernelDebt

noncomputable section

universe u v

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

abbrev TraceSpace := Submodule K (Module.Dual K V)

/-- The persistent direction kernel of a trace packet. -/
def persistentKernel (M : TraceSpace (K := K) (V := V)) : Submodule K V :=
  M.dualCoannihilator

/-- Numerical dimension of the unresolved persistent kernel. -/
def kernelDebt (M : TraceSpace (K := K) (V := V)) : Nat :=
  Module.finrank K (persistentKernel M)

/-- Trace rank and kernel debt exhaust the ambient direction dimension. -/
theorem traceRank_add_kernelDebt
    (M : TraceSpace (K := K) (V := V)) :
    Module.finrank K M + kernelDebt M = Module.finrank K V := by
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq M

/-- Enlarging the trace packet can only shrink the persistent kernel. -/
theorem persistentKernel_antitone
    {M N : TraceSpace (K := K) (V := V)} (hMN : M ≤ N) :
    persistentKernel N ≤ persistentKernel M := by
  exact Submodule.dualCoannihilator_anti hMN

/-- A strict trace-space enlargement strictly lowers kernel dimension. -/
theorem kernelDebt_strict_drop
    {M N : TraceSpace (K := K) (V := V)} (hMN : M < N) :
    kernelDebt N < kernelDebt M := by
  have htrace : Module.finrank K M < Module.finrank K N :=
    Submodule.finrank_lt_finrank_of_lt hMN
  have hM := traceRank_add_kernelDebt M
  have hN := traceRank_add_kernelDebt N
  omega

/-- The persistent kernel itself strictly shrinks under a strict trace-space
enlargement. -/
theorem persistentKernel_strict_shrink
    {M N : TraceSpace (K := K) (V := V)} (hMN : M < N) :
    persistentKernel N < persistentKernel M := by
  have hle : persistentKernel N ≤ persistentKernel M :=
    persistentKernel_antitone hMN.le
  have hdim := kernelDebt_strict_drop hMN
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hfin := congrArg
    (fun Q : Submodule K V => Module.finrank K Q) heq
  exact (Nat.ne_of_lt hdim) hfin

/-- Adjoin one new trace to the packet. -/
def consume (M : TraceSpace (K := K) (V := V))
    (f : Module.Dual K V) : TraceSpace (K := K) (V := V) :=
  M ⊔ Submodule.span K {f}

/-- A trace outside the old packet strictly enlarges it. -/
theorem consume_strict
    {M : TraceSpace (K := K) (V := V)}
    {f : Module.Dual K V} (hf : f ∉ M) :
    M < consume M f := by
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply hf
  have hspan : f ∈ Submodule.span K {f} :=
    Submodule.subset_span (by simp)
  have hmem : f ∈ M ⊔ Submodule.span K {f} :=
    (show Submodule.span K {f} ≤ M ⊔ Submodule.span K {f} from le_sup_right) hspan
  exact heq ▸ hmem

/-- One independent trace increases trace rank by exactly one. -/
theorem traceRank_consume
    {M : TraceSpace (K := K) (V := V)}
    {f : Module.Dual K V} (hf : f ∉ M) :
    Module.finrank K (consume M f) = Module.finrank K M + 1 := by
  simpa [consume] using
    (Submodule.finrank_sup_span_singleton (K := K) (p := M) (v := f) hf)

/-- One independent trace pays exactly one unit of persistent-kernel debt. -/
theorem kernelDebt_consume_add_one
    {M : TraceSpace (K := K) (V := V)}
    {f : Module.Dual K V} (hf : f ∉ M) :
    kernelDebt (consume M f) + 1 = kernelDebt M := by
  have hM := traceRank_add_kernelDebt M
  have hN := traceRank_add_kernelDebt (consume M f)
  have htrace := traceRank_consume hf
  omega

/-- Consequently one independent trace strictly lowers kernel debt. -/
theorem kernelDebt_consume_lt
    {M : TraceSpace (K := K) (V := V)}
    {f : Module.Dual K V} (hf : f ∉ M) :
    kernelDebt (consume M f) < kernelDebt M := by
  have h := kernelDebt_consume_add_one hf
  omega

/-- A certified independent-trace birth. -/
def BirthStep
    (M N : TraceSpace (K := K) (V := V)) : Prop :=
  ∃ f : Module.Dual K V, f ∉ M ∧ N = consume M f

/-- Every certified birth strictly pays kernel debt. -/
theorem birthStep_decreases
    {M N : TraceSpace (K := K) (V := V)} (h : BirthStep M N) :
    kernelDebt N < kernelDebt M := by
  rcases h with ⟨f, hf, rfl⟩
  exact kernelDebt_consume_lt hf

/-- The trace packet is terminal when it has filled the dual space. -/
def Terminal (M : TraceSpace (K := K) (V := V)) : Prop := M = ⊤

/-- Every nonterminal trace packet admits an independent functional. -/
theorem progress (M : TraceSpace (K := K) (V := V)) :
    ¬ Terminal M → ∃ N, BirthStep M N := by
  intro hM
  change M ≠ ⊤ at hM
  have hex : ∃ f : Module.Dual K V, f ∉ M := by
    by_contra hnone
    apply hM
    apply le_antisymm le_top
    intro f hfTop
    by_contra hf
    exact hnone ⟨f, hf⟩
  rcases hex with ⟨f, hf⟩
  exact ⟨consume M f, f, hf, rfl⟩

/-- The independent-trace process compiled by kernel dimension. -/
def program : ResolutionCompiler.Program where
  State := TraceSpace (K := K) (V := V)
  Rank := Nat
  step := BirthStep
  terminal := Terminal
  rank := kernelDebt
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  decreases := birthStep_decreases
  progress := progress

/-- Every initial packet reaches full trace space after finitely many
independent births. -/
theorem reaches_full_trace_space
    (M : TraceSpace (K := K) (V := V)) :
    ∃ N, ResolutionCompiler.Reaches BirthStep M N ∧ N = ⊤ := by
  exact program.terminal_reachable M

/-- No fixed finite-dimensional direction space supports infinitely many
independent trace births. -/
theorem no_infinite_independent_trace_births :
    ¬ ∃ f : Nat → TraceSpace (K := K) (V := V),
      ∀ n, BirthStep (f n) (f (n + 1)) :=
  program.no_infinite_execution

end

end TraceKernelDebt
end PCRLean
