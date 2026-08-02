import Mathlib

/-!
# Morita block-stable submodules

The ideal-descent theorem is the rank-one case of a more general Morita
phenomenon.  On a product coordinate module `(ι × μ) → R`, let the full matrix
algebra on the left index `ι` act fibrewise.  A submodule stable under all left
matrix units is determined by one submodule of the right-row module `μ → R`.

This is the algebraic mechanism needed to descend passive relation modules,
conormal packets, and finite presentations together with active ideals.  It
shows that Cartier/Hasse stability can control modules, not only equations.
-/

namespace PCRLean
namespace BlockMatrixStableSubmodule

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {μ : Type w}
variable [Fintype ι] [DecidableEq ι]

abbrev Row := μ → R
abbrev ProductCoordinates := (ι × μ) → R

/-- Embed one row into the `i`-th left coordinate and put zero in every other
left coordinate. -/
def rowEmbed (i : ι) :
    Row (R := R) (μ := μ) →ₗ[R]
      ProductCoordinates (R := R) (ι := ι) (μ := μ) where
  toFun v p := if p.1 = i then v p.2 else 0
  map_add' := by
    intro x y
    funext p
    by_cases hp : p.1 = i <;> simp [hp]
  map_smul' := by
    intro a x
    funext p
    by_cases hp : p.1 = i <;> simp [hp]

/-- Extract the `i`-th row. -/
def rowAt (i : ι) :
    ProductCoordinates (R := R) (ι := ι) (μ := μ) →ₗ[R]
      Row (R := R) (μ := μ) where
  toFun x m := x (i, m)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

@[simp] theorem rowAt_apply (i : ι)
    (x : ProductCoordinates (R := R) (ι := ι) (μ := μ)) (m : μ) :
    rowAt (R := R) i x m = x (i, m) := rfl

@[simp] theorem rowEmbed_apply (i : ι)
    (v : Row (R := R) (μ := μ)) (p : ι × μ) :
    rowEmbed (R := R) i v p = if p.1 = i then v p.2 else 0 := rfl

/-- Matrix unit on the left coordinate, acting identically on the right row. -/
def leftMatrixUnit (i j : ι) :
    Module.End R (ProductCoordinates (R := R) (ι := ι) (μ := μ)) :=
  (rowEmbed (R := R) i).comp (rowAt (R := R) j)

@[simp] theorem leftMatrixUnit_apply (i j : ι)
    (x : ProductCoordinates (R := R) (ι := ι) (μ := μ))
    (p : ι × μ) :
    leftMatrixUnit (R := R) i j x p =
      if p.1 = i then x (j, p.2) else 0 := rfl

/-- Stability under the full left matrix algebra. -/
def LeftInvariant
    (N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ))) : Prop :=
  ∀ i j x, x ∈ N → leftMatrixUnit (R := R) i j x ∈ N

/-- Common right-row submodule extracted from a left-invariant block
submodule. -/
def rowModule
    (N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ))) :
    Submodule R (Row (R := R) (μ := μ)) where
  carrier := {v | ∀ i, rowEmbed (R := R) i v ∈ N}
  zero_mem' := by
    intro i
    simpa using N.zero_mem
  add_mem' := by
    intro x y hx hy i
    simpa using N.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    simpa using N.smul_mem a (hx i)

@[simp] theorem mem_rowModule_iff
    (N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ)))
    (v : Row (R := R) (μ := μ)) :
    v ∈ rowModule N ↔ ∀ i, rowEmbed (R := R) i v ∈ N :=
  Iff.rfl

/-- Every row of a vector in a left-invariant submodule belongs to the common
row module. -/
theorem row_mem
    {N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ))}
    (hN : LeftInvariant N)
    {x : ProductCoordinates (R := R) (ι := ι) (μ := μ)}
    (hx : x ∈ N) (j : ι) :
    rowAt (R := R) j x ∈ rowModule N := by
  intro i
  exact hN i j x hx

/-- Every product-coordinate vector is the finite sum of its embedded rows. -/
theorem sum_rowEmbed_rowAt
    (x : ProductCoordinates (R := R) (ι := ι) (μ := μ)) :
    (∑ i : ι, rowEmbed (R := R) i (rowAt (R := R) i x)) = x := by
  classical
  ext p
  simp [rowEmbed, rowAt]

/-- If every row lies in the common row module, the whole vector lies in the
original block submodule. -/
theorem mem_of_forall_row_mem
    {N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ))}
    {x : ProductCoordinates (R := R) (ι := ι) (μ := μ)}
    (hx : ∀ i, rowAt (R := R) i x ∈ rowModule N) :
    x ∈ N := by
  rw [← sum_rowEmbed_rowAt (R := R) x]
  exact N.sum_mem fun i _ => (hx i) i

/-- Coordinatewise extension of a right-row submodule. -/
def fromRowModule
    (P : Submodule R (Row (R := R) (μ := μ))) :
    Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ)) where
  carrier := {x | ∀ i, rowAt (R := R) i x ∈ P}
  zero_mem' := by
    intro i
    simpa [rowAt] using P.zero_mem
  add_mem' := by
    intro x y hx hy i
    exact P.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    exact P.smul_mem a (hx i)

@[simp] theorem mem_fromRowModule_iff
    (P : Submodule R (Row (R := R) (μ := μ)))
    (x : ProductCoordinates (R := R) (ι := ι) (μ := μ)) :
    x ∈ fromRowModule (ι := ι) P ↔
      ∀ i, rowAt (R := R) i x ∈ P :=
  Iff.rfl

/-- Every row-extension submodule is invariant under all left matrix units. -/
theorem fromRowModule_leftInvariant
    (P : Submodule R (Row (R := R) (μ := μ))) :
    LeftInvariant (fromRowModule (ι := ι) P) := by
  intro i j x hx a
  by_cases hai : a = i
  · subst a
    have hj := hx j
    simpa [leftMatrixUnit, rowAt, rowEmbed] using hj
  · have hz : rowAt (R := R) a
        (leftMatrixUnit (R := R) i j x) = 0 := by
      funext m
      simp [leftMatrixUnit, rowAt, rowEmbed, hai]
    rw [hz]
    exact P.zero_mem

/-- Morita block classification: a left-invariant submodule is exactly the
coordinatewise extension of one right-row submodule. -/
theorem eq_fromRowModule
    (N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ)))
    (hN : LeftInvariant N) :
    N = fromRowModule (ι := ι) (rowModule N) := by
  ext x
  constructor
  · intro hx i
    exact row_mem hN hx i
  · intro hx
    exact mem_of_forall_row_mem hx

/-- Membership formula for a left-invariant block submodule. -/
theorem mem_iff_forall_row_mem
    {N : Submodule R
      (ProductCoordinates (R := R) (ι := ι) (μ := μ))}
    (hN : LeftInvariant N)
    (x : ProductCoordinates (R := R) (ι := ι) (μ := μ)) :
    x ∈ N ↔ ∀ i, rowAt (R := R) i x ∈ rowModule N := by
  constructor
  · intro hx i
    exact row_mem hN hx i
  · intro hx
    exact mem_of_forall_row_mem hx

end

end BlockMatrixStableSubmodule
end PCRLean