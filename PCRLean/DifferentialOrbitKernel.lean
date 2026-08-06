import Mathlib

/-!
# Differential-orbit kernels

This file formalizes the linear-algebra core of the Hasse--Cartier stable-kernel
idea.  A subspace of dual functionals represents the differential/Hasse orbit
of a quasilinear coefficient packet.  Its common annihilator is the persistent
direction kernel.  If the functional space is stable under precomposition by
an operator, then the persistent kernel is stable under that operator.

The geometric Cartier-descent and actual-centre realization theorems are not
asserted here.
-/

namespace PCRLean
namespace DifferentialOrbitKernel

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]

abbrev Dual := Module.Dual K V

/-- The common annihilator in `V` of a subspace of dual functionals. -/
def annihilator (M : Submodule K (Dual (K := K) (V := V))) : Submodule K V where
  carrier := {x | ∀ f, f ∈ M → f x = 0}
  zero_mem' := by
    intro f hf
    simp
  add_mem' := by
    intro x y hx hy f hf
    rw [map_add, hx f hf, hy f hf, add_zero]
  smul_mem' := by
    intro a x hx f hf
    rw [map_smul, hx f hf, smul_zero]

@[simp] theorem mem_annihilator_iff
    {M : Submodule K (Dual (K := K) (V := V))} {x : V} :
    x ∈ annihilator M ↔ ∀ f, f ∈ M → f x = 0 :=
  Iff.rfl

/-- Enlarging the differential orbit shrinks its persistent kernel. -/
theorem annihilator_antitone
    {M N : Submodule K (Dual (K := K) (V := V))} (hMN : M ≤ N) :
    annihilator N ≤ annihilator M := by
  intro x hx
  rw [mem_annihilator_iff] at hx ⊢
  intro f hf
  exact hx f (hMN hf)

/-- A seed functional in the orbit vanishes on the persistent kernel. -/
theorem annihilator_le_ker_of_mem
    {M : Submodule K (Dual (K := K) (V := V))}
    {f : Dual (K := K) (V := V)} (hf : f ∈ M) :
    annihilator M ≤ LinearMap.ker f := by
  intro x hx
  exact hx f hf

/-- Stability of a dual orbit under precomposition by an operator. -/
def DualStable (D : Module.End K V)
    (M : Submodule K (Dual (K := K) (V := V))) : Prop :=
  ∀ f, f ∈ M → D.dualMap f ∈ M

/-- A dual-stable differential orbit has an invariant persistent kernel. -/
theorem annihilator_invariant
    (D : Module.End K V)
    (M : Submodule K (Dual (K := K) (V := V)))
    (hstable : DualStable D M) :
    ∀ x ∈ annihilator M, D x ∈ annihilator M := by
  intro x hx
  rw [mem_annihilator_iff] at hx ⊢
  intro f hf
  exact hx (D.dualMap f) (hstable f hf)

/-- Simultaneous stability under a family of differential operators. -/
def FamilyStable (ops : ι → Module.End K V)
    (M : Submodule K (Dual (K := K) (V := V))) : Prop :=
  ∀ i, DualStable (ops i) M

/-- The persistent kernel is invariant under every operator in a stable
family. -/
theorem annihilator_family_invariant
    (ops : ι → Module.End K V)
    (M : Submodule K (Dual (K := K) (V := V)))
    (hstable : FamilyStable ops M) :
    ∀ i x, x ∈ annihilator M → ops i x ∈ annihilator M := by
  intro i x hx
  exact annihilator_invariant (ops i) M (hstable i) x hx

/-- Adding one new functional can only shrink the persistent kernel. -/
theorem annihilator_sup_le_left
    (M N : Submodule K (Dual (K := K) (V := V))) :
    annihilator (M ⊔ N) ≤ annihilator M :=
  annihilator_antitone le_sup_left

/-- If a proposed direction survives the enlarged orbit, then it survives each
constituent orbit. -/
theorem mem_both_of_mem_annihilator_sup
    {M N : Submodule K (Dual (K := K) (V := V))} {x : V}
    (hx : x ∈ annihilator (M ⊔ N)) :
    x ∈ annihilator M ∧ x ∈ annihilator N := by
  exact ⟨annihilator_antitone le_sup_left hx,
    annihilator_antitone le_sup_right hx⟩

end

end DifferentialOrbitKernel
end PCRLean
