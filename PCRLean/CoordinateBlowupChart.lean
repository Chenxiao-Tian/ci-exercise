import Mathlib

/-!
# Standard affine charts of a coordinate-centre blowup

Let the ambient polynomial variables be split into passive variables `α` and
centre variables `ι`.  In the standard chart with pivot `k : ι`, the pivot
variable is unchanged and every other centre variable is replaced by the
pivot times a ratio variable.

This file defines the chart homomorphism uniformly for every pivot and proves
that the full centre ideal maps into the pivot ideal.  Consequently the `b`-th
power of the centre maps into the `b`-th power of the exceptional pivot ideal
on every standard chart.  This is the all-chart algebraic divisibility gate for
controlled transforms of coordinate-permissible marked ideals.

Strict-transform saturation and overlap localization are separate obligations.
-/

namespace PCRLean
namespace CoordinateBlowupChart

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [DecidableEq ι]

abbrev Variables := α ⊕ ι
abbrev P := MvPolynomial (Variables (α := α) (ι := ι)) R

/-- A passive ambient coordinate. -/
def passiveVar (a : α) : P (R := R) (α := α) (ι := ι) :=
  MvPolynomial.X (Sum.inl a)

/-- A coordinate vanishing on the blowup centre. -/
def centreVar (i : ι) : P (R := R) (α := α) (ι := ι) :=
  MvPolynomial.X (Sum.inr i)

/-- The actual coordinate centre ideal. -/
noncomputable def centreIdeal : Ideal (P (R := R) (α := α) (ι := ι)) :=
  Ideal.span (Set.range (centreVar (R := R) (α := α) (ι := ι)))

/-- Principal exceptional ideal in the chart with pivot `k`. -/
def pivotIdeal (k : ι) : Ideal (P (R := R) (α := α) (ι := ι)) :=
  Ideal.span {centreVar (R := R) (α := α) (ι := ι) k}

/-- Standard affine chart homomorphism for the blowup of the coordinate
centre.  Nonpivot centre coordinates become pivot times ratio coordinates. -/
def chartMap (k : ι) :
    P (R := R) (α := α) (ι := ι) →+*
      P (R := R) (α := α) (ι := ι) :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun s =>
    match s with
    | Sum.inl a => MvPolynomial.X (Sum.inl a)
    | Sum.inr i =>
        if i = k then MvPolynomial.X (Sum.inr k)
        else MvPolynomial.X (Sum.inr k) * MvPolynomial.X (Sum.inr i)

@[simp] theorem chartMap_passiveVar (k : ι) (a : α) :
    chartMap (R := R) (α := α) k
      (passiveVar (R := R) (ι := ι) a) =
        passiveVar (R := R) (ι := ι) a := by
  simp [chartMap, passiveVar]

@[simp] theorem chartMap_pivot (k : ι) :
    chartMap (R := R) (α := α) k
      (centreVar (R := R) (α := α) k) =
        centreVar (R := R) (α := α) k := by
  simp [chartMap, centreVar]

@[simp] theorem chartMap_nonpivot (k i : ι) (h : i ≠ k) :
    chartMap (R := R) (α := α) k
      (centreVar (R := R) (α := α) i) =
        centreVar (R := R) (α := α) k *
          centreVar (R := R) (α := α) i := by
  simp [chartMap, centreVar, h]

/-- The pivot generator belongs to its exceptional ideal. -/
theorem pivot_mem (k : ι) :
    centreVar (R := R) (α := α) k ∈
      pivotIdeal (R := R) (α := α) k := by
  exact Ideal.mem_span_singleton_self _

/-- Every transformed centre generator belongs to the exceptional pivot
ideal. -/
theorem chartMap_centreVar_mem_pivot (k i : ι) :
    chartMap (R := R) (α := α) k
      (centreVar (R := R) (α := α) i) ∈
        pivotIdeal (R := R) (α := α) k := by
  by_cases h : i = k
  · subst i
    simpa using pivot_mem (R := R) (α := α) k
  · rw [chartMap_nonpivot (R := R) (α := α) k i h]
    exact (pivotIdeal (R := R) (α := α) k).mul_mem_right _
      (pivot_mem (R := R) (α := α) k)

/-- The image of the entire coordinate centre ideal is contained in the
exceptional pivot ideal on every standard chart. -/
theorem map_centreIdeal_le_pivotIdeal (k : ι) :
    (centreIdeal (R := R) (α := α) (ι := ι)).map
        (chartMap (R := R) (α := α) k) ≤
      pivotIdeal (R := R) (α := α) k := by
  rw [Ideal.map_le_iff_le_comap, centreIdeal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  exact chartMap_centreVar_mem_pivot (R := R) (α := α) k i

/-- Powers of the centre map into the corresponding exceptional powers. -/
theorem map_centreIdeal_pow_le_pivotIdeal_pow (k : ι) (b : Nat) :
    ((centreIdeal (R := R) (α := α) (ι := ι)) ^ b).map
        (chartMap (R := R) (α := α) k) ≤
      (pivotIdeal (R := R) (α := α) k) ^ b := by
  rw [Ideal.map_pow]
  gcongr
  exact map_centreIdeal_le_pivotIdeal (R := R) (α := α) k

/-- Elementwise all-chart divisibility consequence. -/
theorem chartMap_mem_pivot_pow
    (k : ι) {b : Nat}
    {f : P (R := R) (α := α) (ι := ι)}
    (hf : f ∈ (centreIdeal (R := R) (α := α) (ι := ι)) ^ b) :
    chartMap (R := R) (α := α) k f ∈
      (pivotIdeal (R := R) (α := α) k) ^ b := by
  apply map_centreIdeal_pow_le_pivotIdeal_pow
    (R := R) (α := α) k b
  exact Ideal.mem_map_of_mem
    (chartMap (R := R) (α := α) k) hf

end

end CoordinateBlowupChart
end PCRLean
