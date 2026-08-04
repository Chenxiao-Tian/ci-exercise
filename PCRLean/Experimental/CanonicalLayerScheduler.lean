import Mathlib

/-!
# Canonical finite layer scheduler

A symmetry-safe wonderful word should not choose one centre from a finite
orbit.  The combinatorial scheduler groups all strata having the same intrinsic
rank into one layer and processes the layers in descending rank.  In geometric
applications the rank is the depth of an intersection stratum (equivalently,
one may use increasing dimension after reversing conventions).

The scheduler is finite, its layers are pairwise disjoint as sets of labels,
and every rank-preserving permutation fixes every layer.  Geometry must still
prove that the transformed centres in one layer are pairwise disjoint and that
their disjoint union is a regular jointly legal ordinary centre.
-/

namespace PCRLean
namespace Experimental
namespace CanonicalLayerScheduler

noncomputable section

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A finite family equipped with a bounded intrinsic natural-number rank. -/
structure RankedFamily where
  rank : α → ℕ
  maxRank : ℕ
  rank_le : ∀ a, rank a ≤ maxRank

namespace RankedFamily

variable (F : RankedFamily (α := α))

/-- The stratum labels of one rank. -/
def layer (k : ℕ) : Finset α :=
  Finset.univ.filter fun a => F.rank a = k

/-- Descending-rank layer schedule. -/
def schedule : List (Finset α) :=
  ((List.range (F.maxRank + 1)).reverse).map F.layer

@[simp] theorem mem_layer_iff (a : α) (k : ℕ) :
    a ∈ F.layer k ↔ F.rank a = k := by
  simp [layer]

/-- Every label belongs to its own rank layer. -/
theorem mem_own_layer (a : α) :
    a ∈ F.layer (F.rank a) := by
  simp [layer]

/-- Distinct rank layers are disjoint. -/
theorem layer_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (F.layer i) (F.layer j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  have hi : F.rank a = i := (F.mem_layer_iff a i).mp hai
  have hj : F.rank a = j := (F.mem_layer_iff a j).mp haj
  exact hij (hi.symm.trans hj)

/-- The schedule has exactly `maxRank + 1` formal layers, including possibly
empty layers. -/
@[simp] theorem schedule_length :
    F.schedule.length = F.maxRank + 1 := by
  simp [schedule]

/-- The rank layer of every label occurs in the schedule. -/
theorem own_layer_mem_schedule (a : α) :
    F.layer (F.rank a) ∈ F.schedule := by
  rw [schedule, List.mem_map]
  refine ⟨F.rank a, ?_, rfl⟩
  rw [List.mem_reverse]
  simp [Nat.lt_succ_iff, F.rank_le a]

/-- A rank-preserving permutation fixes every layer setwise. -/
theorem map_layer_eq
    (e : α ≃ α)
    (hrank : ∀ a, F.rank (e a) = F.rank a)
    (k : ℕ) :
    (F.layer k).map e.toEmbedding = F.layer k := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨b, hb, rfl⟩
    apply (F.mem_layer_iff (e b) k).mpr
    rw [hrank b]
    exact (F.mem_layer_iff b k).mp hb
  · intro ha
    have hpre : e.symm a ∈ F.layer k := by
      apply (F.mem_layer_iff (e.symm a) k).mpr
      have h := hrank (e.symm a)
      rw [e.apply_symm_apply] at h
      rw [← h]
      exact (F.mem_layer_iff a k).mp ha
    exact Finset.mem_map.mpr
      ⟨e.symm a, hpre, e.apply_symm_apply a⟩

/-- Hence a rank-preserving permutation fixes the complete layer schedule. -/
theorem map_schedule_eq
    (e : α ≃ α)
    (hrank : ∀ a, F.rank (e a) = F.rank a) :
    F.schedule.map (fun s => s.map e.toEmbedding) = F.schedule := by
  simp [schedule, F.map_layer_eq e hrank]

end RankedFamily

end

end CanonicalLayerScheduler
end Experimental
end PCRLean
