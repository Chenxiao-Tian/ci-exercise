import Mathlib

/-!
# Matrix-stable submodules of finite free modules

Let `M = ι → R` be a finite free module. A submodule invariant under every
`R`-linear endomorphism of `M` is necessarily obtained coordinatewise from one
ideal of `R`. This is the Morita-theoretic algebraic core of Frobenius descent:
when a smooth characteristic-`p` algebra is finite free over its Frobenius
image, an ideal stable under the full finite-level differential-operator algebra
must descend from the Frobenius base.

This file proves the free-module classification. A geometric application must
identify the finite-level differential operators with the full endomorphism
algebra and transport the result through local Frobenius bases.
-/

namespace PCRLean
namespace MatrixStableSubmodule

noncomputable section

universe u v

variable {R : Type u} {ι : Type v}
variable [CommRing R] [Fintype ι] [DecidableEq ι]

abbrev FreeModule := ι → R

/-- The matrix unit sending the `j`-th coordinate to the `i`-th coordinate and
killing every other coordinate. -/
def matrixUnit (i j : ι) : Module.End R (FreeModule (R := R) (ι := ι)) :=
  (LinearMap.single R (fun _ : ι => R) i).comp
    (LinearMap.proj j : FreeModule (R := R) (ι := ι) →ₗ[R] R)

@[simp] theorem matrixUnit_apply (i j : ι)
    (x : FreeModule (R := R) (ι := ι)) :
    matrixUnit (R := R) i j x = Pi.single i (x j) := rfl

/-- Invariance under the full endomorphism algebra. -/
def FullyInvariant (N : Submodule R (FreeModule (R := R) (ι := ι))) : Prop :=
  ∀ T : Module.End R (FreeModule (R := R) (ι := ι)),
    ∀ x, x ∈ N → T x ∈ N

/-- Scalars whose copy in every coordinate belongs to the invariant submodule. -/
def coordinateIdeal
    (N : Submodule R (FreeModule (R := R) (ι := ι))) : Ideal R where
  carrier := {r | ∀ i, Pi.single i r ∈ N}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro a b ha hb i
    simpa [Pi.single_add] using N.add_mem (ha i) (hb i)
  smul_mem' := by
    intro a b hb i
    change Pi.single i (a • b) ∈ N
    rw [Pi.single_smul]
    exact N.smul_mem a (hb i)

@[simp] theorem mem_coordinateIdeal_iff
    (N : Submodule R (FreeModule (R := R) (ι := ι))) (r : R) :
    r ∈ coordinateIdeal N ↔ ∀ i, Pi.single i r ∈ N := Iff.rfl

/-- Every coordinate of a vector in a fully invariant submodule belongs to the
common coefficient ideal. -/
theorem coordinate_mem
    {N : Submodule R (FreeModule (R := R) (ι := ι))}
    (hN : FullyInvariant N) {x : FreeModule (R := R) (ι := ι)}
    (hx : x ∈ N) (j : ι) :
    x j ∈ coordinateIdeal N := by
  intro i
  have hmap := hN (matrixUnit (R := R) i j) x hx
  simpa using hmap

/-- A vector all of whose coordinates lie in the common coefficient ideal
belongs to the invariant submodule. -/
theorem mem_of_forall_coordinate_mem
    {N : Submodule R (FreeModule (R := R) (ι := ι))}
    {x : FreeModule (R := R) (ι := ι)}
    (hx : ∀ i, x i ∈ coordinateIdeal N) :
    x ∈ N := by
  have hsum : (∑ i, Pi.single i (x i)) = x :=
    LinearMap.sum_single_apply (fun _ : ι => R) x
  rw [← hsum]
  exact N.sum_mem fun i _ => (hx i) i

/-- Classification theorem: membership in a fully invariant submodule is
coordinatewise membership in one ideal of the base ring. -/
theorem mem_iff_forall_coordinate_mem
    {N : Submodule R (FreeModule (R := R) (ι := ι))}
    (hN : FullyInvariant N) (x : FreeModule (R := R) (ι := ι)) :
    x ∈ N ↔ ∀ i, x i ∈ coordinateIdeal N := by
  constructor
  · intro hx i
    exact coordinate_mem hN hx i
  · exact mem_of_forall_coordinate_mem

/-- The coordinatewise submodule attached to an ideal. -/
def fromIdeal (J : Ideal R) :
    Submodule R (FreeModule (R := R) (ι := ι)) where
  carrier := {x | ∀ i, x i ∈ J}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    exact J.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    exact J.mul_mem_left a (hx i)

@[simp] theorem mem_fromIdeal_iff (J : Ideal R)
    (x : FreeModule (R := R) (ι := ι)) :
    x ∈ fromIdeal J ↔ ∀ i, x i ∈ J := Iff.rfl

/-- Every coordinatewise ideal submodule is fully invariant. -/
theorem fromIdeal_fullyInvariant (J : Ideal R) :
    FullyInvariant (fromIdeal (ι := ι) J) := by
  intro T x hx i
  let row : FreeModule (R := R) (ι := ι) →ₗ[R] R :=
    (LinearMap.proj i).comp T
  have hsum : (∑ j, Pi.single j (x j)) = x :=
    LinearMap.sum_single_apply (fun _ : ι => R) x
  have hdecomp : row x = ∑ j, x j * row (Pi.single j 1) := by
    rw [← hsum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul]
    simp [smul_eq_mul, mul_comm]
  rw [show T x i = row x from rfl, hdecomp]
  exact J.sum_mem fun j _ => J.mul_mem_right _ (hx j)

/-- A fully invariant submodule is exactly the coordinatewise extension of its
coefficient ideal. -/
theorem eq_fromIdeal
    (N : Submodule R (FreeModule (R := R) (ι := ι)))
    (hN : FullyInvariant N) :
    N = fromIdeal (coordinateIdeal N) := by
  ext x
  exact mem_iff_forall_coordinate_mem hN x

/-- Recovering the coefficient ideal from its coordinatewise extension. -/
theorem coordinateIdeal_fromIdeal [Nonempty ι] (J : Ideal R) :
    coordinateIdeal (fromIdeal (ι := ι) J) = J := by
  ext r
  constructor
  · intro hr
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    have hi := hr i
    simpa using hi i
  · intro hr i j
    by_cases hji : j = i
    · subst j
      simpa using hr
    · simp [Pi.single_eq_of_ne hji]

end

end MatrixStableSubmodule
end PCRLean
