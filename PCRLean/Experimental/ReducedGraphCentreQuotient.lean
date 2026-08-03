import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity

/-!
# Exact quotient of a polynomial graph centre

For a tuple `h_i ∈ R`, evaluation `Z_i ↦ h_i` is a surjective ring map

`R[Z_i] → R`.

Its kernel is exactly the actual graph ideal `(Z_i-h_i)`.  Consequently the
closed graph centre has coordinate ring exactly `R`.  This provides the
geometric half of the reduced graph model:

* the centre ideal is actual and finitely generated when the normal index is
  finite;
* it is proper over a nontrivial base;
* its quotient is reduced when `R` is reduced; and
* its quotient is regular when `R` is regular.

Together with reduced graph-centre heredity, this yields a complete affine
local certificate except for embedding the chart into a general scheme and
checking owner, boundary and transform conditions.
-/

namespace PCRLean
namespace Experimental
namespace ReducedGraphCentreQuotient

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [DecidableEq ι]

open ReducedPolynomialGraphCentreHeredity

abbrev P := MvPolynomial ι R

/-- Evaluation on the graph. -/
def graphEval (h : ι → R) : P (R := R) (ι := ι) →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) h

@[simp] theorem graphEval_C (h : ι → R) (r : R) :
    graphEval h (MvPolynomial.C r) = r := by
  simp [graphEval]

@[simp] theorem graphEval_X (h : ι → R) (i : ι) :
    graphEval h (MvPolynomial.X i) = h i := by
  simp [graphEval]

@[simp] theorem graphEval_graphGenerator (h : ι → R) (i : ι) :
    graphEval h (graphGenerator h i) = 0 := by
  simp [graphGenerator]

/-- Re-embed the evaluated constant. -/
def constantProjection (h : ι → R) :
    P (R := R) (ι := ι) →+* P :=
  MvPolynomial.C.comp (graphEval h)

@[simp] theorem constantProjection_C (h : ι → R) (r : R) :
    constantProjection h (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [constantProjection]

@[simp] theorem constantProjection_X (h : ι → R) (i : ι) :
    constantProjection h (MvPolynomial.X i) = MvPolynomial.C (h i) := by
  simp [constantProjection]

/-- Every polynomial differs from its graph value by an element of the graph
ideal. -/
theorem sub_constantProjection_mem
    (h : ι → R) (p : P (R := R) (ι := ι)) :
    p - constantProjection h p ∈ graphIdeal h := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [constantProjection]
  | add p q hp hq =>
      have hadd := (graphIdeal h).add_mem hp hq
      simpa [map_add, add_sub_add_comm] using hadd
  | mul_X p i hp =>
      have hleft :
          (p - constantProjection h p) * MvPolynomial.X i ∈ graphIdeal h :=
        (graphIdeal h).mul_mem_right _ hp
      have hright :
          constantProjection h p * graphGenerator h i ∈ graphIdeal h :=
        (graphIdeal h).mul_mem_left _ (graphGenerator_mem h i)
      have hadd := (graphIdeal h).add_mem hleft hright
      have heq :
          p * MvPolynomial.X i - constantProjection h (p * MvPolynomial.X i) =
            (p - constantProjection h p) * MvPolynomial.X i +
              constantProjection h p * graphGenerator h i := by
        simp [constantProjection, graphGenerator]
        ring
      rw [heq]
      exact hadd

/-- The graph ideal is contained in the evaluation kernel. -/
theorem graphIdeal_le_ker (h : ι → R) :
    graphIdeal h ≤ RingHom.ker (graphEval h) := by
  rw [graphIdeal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  exact graphEval_graphGenerator h i

/-- Exact kernel theorem for the graph evaluation map. -/
theorem ker_graphEval_eq_graphIdeal (h : ι → R) :
    RingHom.ker (graphEval h) = graphIdeal h := by
  apply le_antisymm
  · intro p hp
    have hzero : graphEval h p = 0 := RingHom.mem_ker.mp hp
    have hmem := sub_constantProjection_mem h p
    simpa [constantProjection, hzero] using hmem
  · exact graphIdeal_le_ker h

/-- Graph evaluation is surjective. -/
theorem graphEval_surjective (h : ι → R) :
    Function.Surjective (graphEval h) := by
  intro r
  exact ⟨MvPolynomial.C r, by simp⟩

/-- Exact quotient theorem for the actual graph centre. -/
noncomputable def quotientEquiv (h : ι → R) :
    (P (R := R) (ι := ι) ⧸ graphIdeal h) ≃+* R :=
  (Ideal.quotEquivOfEq (ker_graphEval_eq_graphIdeal h).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := graphEval h) (graphEval_surjective h))

/-- The quotient equivalence evaluates representatives on the graph. -/
@[simp] theorem quotientEquiv_mk
    (h : ι → R) (p : P (R := R) (ι := ι)) :
    quotientEquiv h (Ideal.Quotient.mk (graphIdeal h) p) = graphEval h p := by
  simp [quotientEquiv]

/-- A graph ideal is proper over a nontrivial base. -/
theorem graphIdeal_ne_top [Nontrivial R] (h : ι → R) :
    graphIdeal h ≠ ⊤ := by
  intro htop
  have hunit : (1 : P (R := R) (ι := ι)) ∈ graphIdeal h := by
    rw [htop]
    trivial
  have hker := graphIdeal_le_ker h hunit
  have hzero := RingHom.mem_ker.mp hker
  simpa using hzero

/-- A graph ideal has a finite generating set when the normal index is finite. -/
theorem graphIdeal_fg [Finite ι] (h : ι → R) :
    (graphIdeal h).FG := by
  rw [graphIdeal]
  exact Submodule.fg_span (Set.finite_range _)

/-- Reducedness of the base transfers to the graph centre quotient. -/
theorem quotient_isReduced [IsReduced R] (h : ι → R) :
    IsReduced (P (R := R) (ι := ι) ⧸ graphIdeal h) := by
  exact isReduced_of_injective (quotientEquiv h).toRingHom
    (quotientEquiv h).injective

/-- Regularity of the base transfers to the graph centre quotient. -/
theorem quotient_isRegularRing [IsRegularRing R] (h : ι → R) :
    IsRegularRing (P (R := R) (ι := ι) ⧸ graphIdeal h) := by
  exact IsRegularRing.of_ringEquiv (quotientEquiv h).symm

end

end ReducedGraphCentreQuotient
end Experimental
end PCRLean
