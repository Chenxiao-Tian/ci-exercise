import Mathlib

/-!
# Experimental left-summand coordinate blowup charts

This is the left-summand analogue of `CoordinateBlowupChart`.  Variables are
split as centre variables `ι` followed by passive variables `α`.  In the chart
with pivot `k`, the pivot is fixed, nonpivot centre variables become pivot times
ratio variables, and passive variables are fixed.

The variant matches the basis-extension coordinates used by
`DualPacketCoordinateNormalization`.
-/

namespace PCRLean
namespace Experimental
namespace LeftCoordinateBlowupChart

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {α : Type w}
variable [DecidableEq ι]

abbrev Variables := ι ⊕ α
abbrev P := MvPolynomial (Variables (ι := ι) (α := α)) R

/-- A coordinate vanishing on the centre. -/
def centreVar (i : ι) : P (R := R) (ι := ι) (α := α) :=
  MvPolynomial.X (Sum.inl i)

/-- A passive ambient coordinate. -/
def passiveVar (a : α) : P (R := R) (ι := ι) (α := α) :=
  MvPolynomial.X (Sum.inr a)

/-- Actual left-summand coordinate centre ideal. -/
noncomputable def centreIdeal : Ideal (P (R := R) (ι := ι) (α := α)) :=
  Ideal.span (Set.range (centreVar (R := R) (ι := ι) (α := α)))

/-- Standard pivot chart endomorphism. -/
def chartMap (k : ι) :
    P (R := R) (ι := ι) (α := α) →+*
      P (R := R) (ι := ι) (α := α) :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun s =>
    match s with
    | Sum.inl i =>
        if i = k then MvPolynomial.X (Sum.inl k)
        else MvPolynomial.X (Sum.inl k) * MvPolynomial.X (Sum.inl i)
    | Sum.inr a => MvPolynomial.X (Sum.inr a)

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

@[simp] theorem chartMap_passiveVar (k : ι) (a : α) :
    chartMap (R := R) (ι := ι) k
        (passiveVar (R := R) (ι := ι) a) =
      passiveVar (R := R) (ι := ι) a := by
  simp [chartMap, passiveVar]

/-- Controlled root of one centre coordinate. -/
def controlledRoot (k i : ι) :
    P (R := R) (ι := ι) (α := α) :=
  if i = k then 1 else centreVar (R := R) (α := α) i

/-- Exact pivot factorization of every centre variable. -/
theorem centreVar_factorization (k i : ι) :
    chartMap (R := R) (α := α) k
        (centreVar (R := R) (α := α) i) =
      centreVar (R := R) (α := α) k *
        controlledRoot (R := R) (α := α) k i := by
  by_cases h : i = k
  · subst i
    simp [controlledRoot]
  · simp [controlledRoot, h, chartMap_nonpivot]

/-- Exact powered factorization. -/
theorem centreVar_pow_factorization (k i : ι) (q : Nat) :
    chartMap (R := R) (α := α) k
        ((centreVar (R := R) (α := α) i) ^ q) =
      (centreVar (R := R) (α := α) k) ^ q *
        (controlledRoot (R := R) (α := α) k i) ^ q := by
  rw [map_pow, centreVar_factorization, mul_pow]

/-- Controlled full root ideal. -/
def transformedRootIdeal (k : ι) (q : Nat) :
    Ideal (P (R := R) (ι := ι) (α := α)) :=
  Ideal.span (Set.range fun i : ι =>
    (controlledRoot (R := R) (α := α) k i) ^ q)

/-- Every pivot chart makes the full controlled root ideal terminal. -/
theorem transformedRootIdeal_eq_top (k : ι) (q : Nat) :
    transformedRootIdeal (R := R) (α := α) k q = ⊤ := by
  apply top_unique
  intro x hx
  have h1 : (1 : P (R := R) (ι := ι) (α := α)) ∈
      transformedRootIdeal (R := R) (α := α) k q := by
    apply Ideal.subset_span
    refine ⟨k, ?_⟩
    simp [controlledRoot]
  simpa using
    (transformedRootIdeal (R := R) (α := α) k q).mul_mem_left x h1

end

end LeftCoordinateBlowupChart
end Experimental
end PCRLean
