import Mathlib

/-!
# The symmetric configuration-difference packet

On a common graph chart, a finite family of regular centres is represented by
sections `h_a` of one normal module.  Their common intersection is governed by
the equalizer equations `h_a = h_b`.  Rather than choosing a distinguished
base centre, collect every ordered difference

`D(h)_(a,b) = h_a - h_b`.

This is a canonical linear packet, equivariant under every permutation of the
family.  Its kernel is exactly the diagonal submodule of constant families.
Thus multi-centre coincidence and contact can be fed back into the same finite
packet/order-ideal/Hasse machinery as the original resolution state.

The geometric theorem identifying an arbitrary étale graph-atlas intersection
with this packet, and the strict descent theorem for a nonregular difference
zero scheme, remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace SymmetricConfigurationDifference

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {α : Type w} [Fintype α]

/-- The diagonal embedding of one section as a constant finite family. -/
def diagonal : N →ₗ[R] (α → N) where
  toFun x := fun _ => x
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

/-- All ordered pairwise differences of a finite family. -/
def pairwiseDifference : (α → N) →ₗ[R] (α × α → N) where
  toFun h := fun ij => h ij.1 - h ij.2
  map_add' := by
    intro h k
    ext ij
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro r h
    ext ij
    simp [smul_sub]

@[simp] theorem pairwiseDifference_apply
    (h : α → N) (i j : α) :
    pairwiseDifference h (i, j) = h i - h j := rfl

/-- Vanishing of the difference packet is exactly pairwise equality. -/
theorem mem_ker_pairwiseDifference_iff
    (h : α → N) :
    h ∈ LinearMap.ker (pairwiseDifference (R := R) (N := N) (α := α)) ↔
      ∀ i j, h i = h j := by
  constructor
  · intro hh i j
    have hz := congrFun (LinearMap.mem_ker.mp hh) (i, j)
    simpa [pairwiseDifference] using sub_eq_zero.mp hz
  · intro hh
    apply LinearMap.mem_ker.mpr
    ext ij
    simp [pairwiseDifference, hh ij.1 ij.2]

/-- Every diagonal family lies in the difference kernel. -/
theorem range_diagonal_le_ker :
    LinearMap.range (diagonal (R := R) (N := N) (α := α)) ≤
      LinearMap.ker (pairwiseDifference (R := R) (N := N) (α := α)) := by
  rintro h ⟨x, rfl⟩
  exact (mem_ker_pairwiseDifference_iff (R := R) (N := N)
    (fun _ : α => x)).mpr fun _ _ => rfl

/-- For a nonempty family, the difference kernel is exactly the diagonal
submodule. -/
theorem ker_pairwiseDifference_eq_range_diagonal
    [Nonempty α] :
    LinearMap.ker (pairwiseDifference (R := R) (N := N) (α := α)) =
      LinearMap.range (diagonal (R := R) (N := N) (α := α)) := by
  apply le_antisymm
  · intro h hh
    classical
    let a0 : α := Classical.choice inferInstance
    refine ⟨h a0, ?_⟩
    ext i
    have heq :=
      (mem_ker_pairwiseDifference_iff (R := R) (N := N) h).mp hh i a0
    simpa [diagonal] using heq.symm
  · exact range_diagonal_le_ker (R := R) (N := N) (α := α)

/-- Equivalently, every zero-difference family is constant. -/
theorem pairwiseDifference_eq_zero_iff_constant
    [Nonempty α] (h : α → N) :
    pairwiseDifference h = 0 ↔
      ∃ x : N, h = fun _ => x := by
  constructor
  · intro hh
    have hker : h ∈ LinearMap.ker
        (pairwiseDifference (R := R) (N := N) (α := α)) :=
      LinearMap.mem_ker.mpr hh
    rw [ker_pairwiseDifference_eq_range_diagonal
      (R := R) (N := N) (α := α)] at hker
    rcases hker with ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    ext ij
    simp [pairwiseDifference]

/-- Reindexing the finite family merely reindexes the pairwise-difference
packet.  No distinguished minimizer is chosen. -/
theorem pairwiseDifference_permute
    (e : α ≃ α) (h : α → N) (i j : α) :
    pairwiseDifference (fun a => h (e.symm a)) (i, j) =
      pairwiseDifference h (e.symm i, e.symm j) := rfl

end

end SymmetricConfigurationDifference
end Experimental
end PCRLean
