import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.PolynomialGraphCentreHeredity

/-!
# Exact quotient and regularity of polynomial graph centres

Let `R` be a domain and let `h : ι → R`.  In `R[Z_i]`, the equations

`Z_i - h_i = 0`

define the graph of `h`.  This file proves directly that evaluation at `h`
has kernel exactly the graph ideal, and hence that the quotient by the actual
graph ideal is the coefficient ring `R`.

Consequently, over a Noetherian regular coefficient ring with finitely many
normal variables, the graph ideal is a proper finitely generated actual ideal
whose closed affine centre has regular coordinate ring.

This is a regular-centre theorem, not yet a theorem that the embedding is a
regular immersion in an arbitrary ambient scheme.  Scheme-level conormal
freeness, boundary transversality, passive safety and hereditary blowup
transport remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphCentreQuotient

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]

open PolynomialGraphCentreHeredity

abbrev P := MvPolynomial ι R

/-- Evaluation on the graph `Z_i = h_i`. -/
def graphEval (h : ι → R) : P (R := R) (ι := ι) →+* R :=
  MvPolynomial.eval₂Hom (RingHom.id R) h

@[simp] theorem graphEval_C (h : ι → R) (r : R) :
    graphEval h (MvPolynomial.C r) = r := by
  simp [graphEval]

@[simp] theorem graphEval_X (h : ι → R) (i : ι) :
    graphEval h (MvPolynomial.X i) = h i := by
  simp [graphEval]

/-- Projection onto constant polynomials by evaluation on the graph. -/
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
    (h : ι → R) (f : P (R := R) (ι := ι)) :
    f - constantProjection h f ∈ graphIdeal h := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg =>
      have hadd := (graphIdeal h).add_mem hf hg
      simpa [map_add, add_sub_add_comm] using hadd
  | mul_X f i hf =>
      have h1 :
          (f - constantProjection h f) * MvPolynomial.X i ∈
            graphIdeal h :=
        (graphIdeal h).mul_mem_right _ hf
      have h2 :
          constantProjection h f * graphGenerator h i ∈ graphIdeal h :=
        (graphIdeal h).mul_mem_left _ (graphGenerator_mem h i)
      have hadd := (graphIdeal h).add_mem h1 h2
      have heq :
          f * MvPolynomial.X i -
              constantProjection h (f * MvPolynomial.X i) =
            (f - constantProjection h f) * MvPolynomial.X i +
              constantProjection h f * graphGenerator h i := by
        simp [constantProjection, graphGenerator]
        ring
      rw [heq]
      exact hadd

/-- The graph ideal is contained in the evaluation kernel. -/
theorem graphIdeal_le_ker
    (h : ι → R) :
    graphIdeal h ≤ RingHom.ker (graphEval h) := by
  rw [graphIdeal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  simp [graphEval, graphGenerator]

/-- Evaluation has no additional kernel: the kernel is exactly the actual graph
ideal. -/
theorem ker_graphEval_eq_graphIdeal
    (h : ι → R) :
    RingHom.ker (graphEval h) = graphIdeal h := by
  apply le_antisymm
  · intro f hf
    have hzero : graphEval h f = 0 := RingHom.mem_ker.mp hf
    have hmem := sub_constantProjection_mem h f
    simpa [constantProjection, hzero] using hmem
  · exact graphIdeal_le_ker h

/-- Evaluation on the graph is surjective. -/
theorem graphEval_surjective
    (h : ι → R) : Function.Surjective (graphEval h) := by
  intro r
  exact ⟨MvPolynomial.C r, by simp [graphEval]⟩

/-- Exact quotient by the actual polynomial graph centre. -/
noncomputable def quotientEquiv
    (h : ι → R) :
    (P (R := R) (ι := ι) ⧸ graphIdeal h) ≃+* R :=
  (Ideal.quotEquivOfEq (ker_graphEval_eq_graphIdeal h).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := graphEval h) (graphEval_surjective h))

@[simp] theorem quotientEquiv_mk
    (h : ι → R) (f : P (R := R) (ι := ι)) :
    quotientEquiv h (Ideal.Quotient.mk (graphIdeal h) f) = graphEval h f := by
  simp [quotientEquiv]

/-- Regularity of the coefficient ring transfers to the graph centre. -/
theorem quotient_isRegularRing
    [IsRegularRing R] (h : ι → R) :
    IsRegularRing (P (R := R) (ι := ι) ⧸ graphIdeal h) := by
  exact IsRegularRing.of_ringEquiv (quotientEquiv h).symm

/-- One affine actual-centre certificate for a polynomial graph. -/
structure Certificate (h : ι → R) where
  ideal : Ideal (P (R := R) (ι := ι))
  ideal_eq : ideal = graphIdeal h
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient : (P (R := R) (ι := ι) ⧸ ideal) ≃+* R
  quotientRegular : IsRegularRing (P (R := R) (ι := ι) ⧸ ideal)

/-- Assemble the proper finite-type regular graph-centre certificate. -/
noncomputable def certificate
    [IsNoetherianRing R] [IsRegularRing R] [Finite ι]
    (h : ι → R) : Certificate h where
  ideal := graphIdeal h
  ideal_eq := rfl
  proper := graphIdeal_ne_top h
  finiteType := graphIdeal_fg h
  quotient := quotientEquiv h
  quotientRegular := quotient_isRegularRing h

end

end PolynomialGraphCentreQuotient
end Experimental
end PCRLean
