import Mathlib
import PCRLean.Experimental.LinearSplitCentreQuotient
import PCRLean.CoordinateRootPacket

/-!
# Experimental all-chart blowup of a transported linear centre

A full linear frame identifies an arbitrary split linear centre with the
standard coordinate centre.  Conjugating every standard coordinate blowup
chart by the polynomial automorphism gives the corresponding chart maps for the
transported centre.

The standard coordinate factorization, exceptional divisibility, terminal root
packet, and pairwise chart agreement then transport exactly.  This closes the
all-chart controlled-transform theorem for the full linear chamber.  It does
not construct a full frame from an arbitrary Frobenius/Fitting core, address
nonlinear higher-order centre equations, or prove scheme-level localization
and gluing.
-/

namespace PCRLean
namespace Experimental
namespace LinearSplitCentreBlowup

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]

abbrev P := MvPolynomial (α ⊕ ι) K

variable (F : LinearCoordinateChange.FullFrame
  (K := K) (σ := α ⊕ ι))

/-- Transported passive coordinate. -/
def linearPassiveVar (a : α) : P (K := K) (α := α) (ι := ι) :=
  F.forward (CoordinateBlowupChart.passiveVar (R := K) (ι := ι) a)

/-- Transported centre coordinate. -/
def linearCentreVar (i : ι) : P (K := K) (α := α) (ι := ι) :=
  F.forward (CoordinateBlowupChart.centreVar (R := K) (α := α) i)

/-- The transported centre written directly as the span of its linear
coordinate generators. -/
def linearCentreSpan : Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.span (Set.range fun i : ι =>
    linearCentreVar (K := K) (α := α) F i)

/-- Principal exceptional ideal in the transported chart with pivot `k`. -/
def linearPivotIdeal (k : ι) :
    Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.span {linearCentreVar (K := K) (α := α) F k}

/-- Conjugate a standard coordinate chart by the full linear polynomial
automorphism. -/
def linearChartMap (k : ι) :
    P (K := K) (α := α) (ι := ι) →+*
      P (K := K) (α := α) (ι := ι) :=
  F.forward.toRingHom.comp
    ((CoordinateBlowupChart.chartMap (R := K) (α := α) k).comp
      F.inverse.toRingHom)

/-- Controlled root transform transported through the linear frame. -/
def linearRootTransform (k i : ι) :
    P (K := K) (α := α) (ι := ι) :=
  F.forward
    (CoordinateRootPacket.explicitRootTransform
      (R := K) (α := α) k i)

/-- Conjugation identity on every polynomial expressed in coordinate-frame
variables. -/
theorem linearChartMap_forward (k : ι)
    (p : P (K := K) (α := α) (ι := ι)) :
    linearChartMap (K := K) (α := α) F k (F.forward p) =
      F.forward (CoordinateBlowupChart.chartMap
        (R := K) (α := α) k p) := by
  have hcomp := congrArg
    (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
        P (K := K) (α := α) (ι := ι) => H p)
    F.inverse_comp_forward
  have hinv : F.inverse (F.forward p) = p := by
    simpa using hcomp
  simp [linearChartMap, hinv]

/-- The direct generator-span definition agrees with the transported ideal used
by the quotient theorem. -/
theorem linearCentreSpan_eq_linearCentreIdeal :
    linearCentreSpan (K := K) (α := α) F =
      LinearSplitCentreQuotient.linearCentreIdeal
        (K := K) (α := α) (ι := ι) F := by
  apply le_antisymm
  · rw [linearCentreSpan, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem F.forward
      (Ideal.subset_span ⟨i, rfl⟩)
  · rw [LinearSplitCentreQuotient.linearCentreIdeal,
      LinearSplitCentreQuotient.coordinateCentreIdeal,
      Ideal.map_le_iff_le_comap,
      CoordinateBlowupChart.centreIdeal,
      Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    exact Ideal.subset_span ⟨i, rfl⟩

/-- The transported pivot generator belongs to its exceptional ideal. -/
theorem linearPivot_mem (k : ι) :
    linearCentreVar (K := K) (α := α) F k ∈
      linearPivotIdeal (K := K) (α := α) F k := by
  exact Ideal.mem_span_singleton_self _

/-- Every transported passive coordinate is fixed by every conjugated chart. -/
theorem linearPassiveVar_fixed (k : ι) (a : α) :
    linearChartMap (K := K) (α := α) F k
        (linearPassiveVar (K := K) (α := α) F a) =
      linearPassiveVar (K := K) (α := α) F a := by
  rw [linearPassiveVar, linearChartMap_forward]
  simp

/-- Exact factorization of every transported linear centre generator. -/
theorem linearCentreVar_factorization (k i : ι) :
    linearChartMap (K := K) (α := α) F k
        (linearCentreVar (K := K) (α := α) F i) =
      linearCentreVar (K := K) (α := α) F k *
        linearRootTransform (K := K) (α := α) F k i := by
  rw [linearCentreVar, linearChartMap_forward,
    CoordinateRootPacket.centreVar_factorization]
  simp [linearCentreVar, linearRootTransform]

/-- Exact factorization of transported `q`-th powers. -/
theorem linearCentreVar_pow_factorization (k i : ι) (q : Nat) :
    linearChartMap (K := K) (α := α) F k
        ((linearCentreVar (K := K) (α := α) F i) ^ q) =
      (linearCentreVar (K := K) (α := α) F k) ^ q *
        (linearRootTransform (K := K) (α := α) F k i) ^ q := by
  rw [map_pow, linearCentreVar_factorization, mul_pow]

/-- Every transformed generator belongs to the transported exceptional pivot
ideal. -/
theorem linearChartMap_centreVar_mem_pivot (k i : ι) :
    linearChartMap (K := K) (α := α) F k
        (linearCentreVar (K := K) (α := α) F i) ∈
      linearPivotIdeal (K := K) (α := α) F k := by
  rw [linearCentreVar_factorization]
  exact (linearPivotIdeal (K := K) (α := α) F k).mul_mem_right _
    (linearPivot_mem (K := K) (α := α) F k)

/-- The complete transported centre maps into the exceptional pivot ideal on
every conjugated standard chart. -/
theorem map_linearCentreSpan_le_linearPivotIdeal (k : ι) :
    (linearCentreSpan (K := K) (α := α) F).map
        (linearChartMap (K := K) (α := α) F k) ≤
      linearPivotIdeal (K := K) (α := α) F k := by
  rw [Ideal.map_le_iff_le_comap, linearCentreSpan, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  rw [Ideal.mem_comap]
  exact linearChartMap_centreVar_mem_pivot
    (K := K) (α := α) F k i

/-- Powers of the transported centre map into corresponding exceptional
powers. -/
theorem map_linearCentreSpan_pow_le_linearPivotIdeal_pow
    (k : ι) (q : Nat) :
    ((linearCentreSpan (K := K) (α := α) F) ^ q).map
        (linearChartMap (K := K) (α := α) F k) ≤
      (linearPivotIdeal (K := K) (α := α) F k) ^ q := by
  rw [Ideal.map_pow]
  gcongr
  exact map_linearCentreSpan_le_linearPivotIdeal
    (K := K) (α := α) F k

/-- Controlled root packet in one transported chart. -/
def transformedLinearRootIdeal (k : ι) (q : Nat) :
    Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.span (Set.range fun i : ι =>
    (linearRootTransform (K := K) (α := α) F k i) ^ q)

/-- The pivot root transforms to the unit. -/
theorem one_mem_transformedLinearRootIdeal (k : ι) (q : Nat) :
    (1 : P (K := K) (α := α) (ι := ι)) ∈
      transformedLinearRootIdeal (K := K) (α := α) F k q := by
  apply Ideal.subset_span
  refine ⟨k, ?_⟩
  simp [linearRootTransform,
    CoordinateRootPacket.explicitRootTransform]

/-- The transported full root packet is terminal on every conjugated standard
chart. -/
theorem transformedLinearRootIdeal_eq_top (k : ι) (q : Nat) :
    transformedLinearRootIdeal (K := K) (α := α) F k q = ⊤ := by
  apply top_unique
  intro x hx
  have h1 := one_mem_transformedLinearRootIdeal
    (K := K) (α := α) F k q
  simpa using
    (transformedLinearRootIdeal (K := K) (α := α) F k q).mul_mem_left x h1

/-- Terminal transported root packets agree pairwise on all charts. -/
theorem transformedLinearRootIdeal_eq (i j : ι) (q : Nat) :
    transformedLinearRootIdeal (K := K) (α := α) F i q =
      transformedLinearRootIdeal (K := K) (α := α) F j q := by
  rw [transformedLinearRootIdeal_eq_top,
    transformedLinearRootIdeal_eq_top]

end

end LinearSplitCentreBlowup
end Experimental
end PCRLean
