import Mathlib

/-!
# Finite-projective Morita submodule descent

A finite dual frame replaces a chosen basis. If a submodule is stable under
all rank-one operators built from the frame, it is generated from one scalar
ideal. This is the coordinate-free form of matrix-stable row descent.

The file deliberately assumes an explicit dual frame. A later projective API
bridge should construct it from finite projectivity and use faithful flatness
to prove overlap uniqueness.
-/

namespace PCRLean
namespace Experimental
namespace ProjectiveMoritaDescent

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- A finite dual frame for a projective module. -/
structure DualFrame where
  vector : ι → P
  functional : ι → P →ₗ[R] R
  reconstruct : ∀ x : P,
    (∑ i : ι, (functional i x) • vector i) = x

namespace DualFrame

variable (F : DualFrame (R := R) (P := P) (ι := ι))

/-- Rank-one operator associated to two frame indices. -/
def rankOne (i j : ι) : Module.End R P where
  toFun x := (F.functional i x) • F.vector j
  map_add' := by
    intro x y
    simp [add_smul]
  map_smul' := by
    intro a x
    simp [mul_smul]

/-- Stability under every frame rank-one operator. -/
def Stable (N : Submodule R P) : Prop :=
  ∀ i j x, x ∈ N → F.rankOne i j x ∈ N

/-- Coefficient ideal extracted from a stable submodule. -/
def coefficientIdeal (N : Submodule R P) : Ideal R :=
  Ideal.span (Set.range fun z : ι × N => F.functional z.1 z.2.1)

/-- Every frame coefficient of a member of `N` lies in the coefficient ideal. -/
theorem coefficient_mem
    (N : Submodule R P) (i : ι) {x : P} (hx : x ∈ N) :
    F.functional i x ∈ F.coefficientIdeal N := by
  apply Ideal.subset_span
  exact ⟨⟨i, ⟨x, hx⟩⟩, rfl⟩

/-- Every member of `N` lies in the scalar extension of its coefficient ideal. -/
theorem le_coefficient_smul_top (N : Submodule R P) :
    N ≤ F.coefficientIdeal N • (⊤ : Submodule R P) := by
  intro x hx
  rw [← F.reconstruct x]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (F.coefficient_mem N i hx) Submodule.mem_top

/-- A coefficient generator multiplied by a frame vector belongs to a stable
submodule. -/
theorem coefficient_generator_smul_vector_mem
    (N : Submodule R P) (hN : F.Stable N)
    (i j : ι) {x : P} (hx : x ∈ N) :
    (F.functional i x) • F.vector j ∈ N := by
  exact hN i j x hx

/-- Stability under rank-one operators forces scalar extension from one ideal. -/
theorem coefficient_smul_top_le
    (N : Submodule R P) (hN : F.Stable N) :
    F.coefficientIdeal N • (⊤ : Submodule R P) ≤ N := by
  rw [Submodule.smul_le]
  intro a ha y hy
  induction ha using Submodule.span_induction with
  | mem a ha =>
      rcases ha with ⟨z, rfl⟩
      rw [← F.reconstruct y, smul_sum]
      exact N.sum_mem fun j _ => by
        rw [smul_smul]
        exact N.smul_mem (F.functional j y)
          (F.coefficient_generator_smul_vector_mem
            N hN z.1 j z.2.2)
  | zero => simp
  | add a b ha hb iha ihb =>
      simpa [add_smul] using N.add_mem iha ihb
  | smul r a ha iha =>
      simpa [smul_eq_mul, mul_smul] using N.smul_mem r iha

/-- Coordinate-free Morita classification for a finite dual frame. -/
theorem eq_coefficientIdeal_smul_top
    (N : Submodule R P) (hN : F.Stable N) :
    N = F.coefficientIdeal N • (⊤ : Submodule R P) := by
  apply le_antisymm
  · exact F.le_coefficient_smul_top N
  · exact F.coefficient_smul_top_le N hN

end DualFrame

end

end ProjectiveMoritaDescent
end Experimental
end PCRLean
