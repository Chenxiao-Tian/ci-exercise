import Mathlib
import Mathlib.RingTheory.Ideal.Cotangent
import PCRLean.Experimental.CoordinateCentreCotangentBasis
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity

/-!
# Cotangent basis of a polynomial graph centre

For the graph ideal

`I_h = (Z_i - h_i) ⊂ R[Z_i]`,

translation sends `I_h` to the coordinate ideal `(Z_i)`.  The degree-one
coefficient rows after translation therefore identify the conormal module
`I_h/I_h²` with the free module `ι → R`.

This gives a nonlinear local regular-immersion certificate: the actual graph
ideal has an explicit free conormal basis, independently of characteristic or
reducedness.  Reducedness enters only in the separate Frobenius-normality
theorem.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphCentreCotangentBasis

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

open ReducedPolynomialGraphCentreHeredity

abbrev P := MvPolynomial ι R
abbrev GraphI (h : ι → R) : Ideal (P (R := R) (ι := ι)) :=
  graphIdeal h
abbrev OriginI : Ideal (P (R := R) (ι := ι)) :=
  originIdeal (R := R) (ι := ι)

/-- Translation carries a graph-ideal element to the coordinate ideal. -/
def translatedElement (h : ι → R)
    (x : GraphI (R := R) (ι := ι) h) :
    OriginI (R := R) (ι := ι) :=
  ⟨translate h x.1, by
    have hm := Ideal.mem_map_of_mem (translate h) x.2
    rw [map_graphIdeal_eq_originIdeal] at hm
    exact hm⟩

/-- Linear coefficient rows of a graph-ideal element after graph translation. -/
def graphLinearCoefficients (h : ι → R) :
    GraphI (R := R) (ι := ι) h →ₗ[R] (ι → R) where
  toFun x := CoordinateCentreCotangentBasis.linearCoefficients
    (R := R) (ι := ι) (translatedElement h x)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

/-- Products in the graph ideal have zero translated degree-one row. -/
theorem graphLinearCoefficients_mul_zero
    (h : ι → R)
    (x y : GraphI (R := R) (ι := ι) h) :
    graphLinearCoefficients (R := R) (ι := ι) h (x * y) = 0 := by
  have hxy := CoordinateCentreCotangentBasis.linearCoefficients_mul_zero
    (R := R) (ι := ι)
    (translatedElement h x) (translatedElement h y)
  simpa [graphLinearCoefficients, translatedElement, map_mul] using hxy

/-- Coefficient-row map on the graph conormal module. -/
def toRows (h : ι → R) :
    (GraphI (R := R) (ι := ι) h).Cotangent →ₗ[R] (ι → R) :=
  Ideal.Cotangent.lift
    (graphLinearCoefficients (R := R) (ι := ι) h)
    (graphLinearCoefficients_mul_zero (R := R) (ι := ι) h)

/-- Class of one graph equation in `I_h/I_h²`. -/
def graphGeneratorClass (h : ι → R) (i : ι) :
    (GraphI (R := R) (ι := ι) h).Cotangent :=
  (GraphI (R := R) (ι := ι) h).toCotangent
    ⟨graphGenerator h i, graphGenerator_mem h i⟩

@[simp] theorem toRows_graphGeneratorClass
    (h : ι → R) (i j : ι) :
    toRows (R := R) (ι := ι) h
        (graphGeneratorClass (R := R) (ι := ι) h i) j =
      if j = i then 1 else 0 := by
  simp [toRows, graphGeneratorClass, graphLinearCoefficients,
    translatedElement, CoordinateCentreCotangentBasis.linearCoefficients]

/-- Every row is represented by the corresponding combination of graph
generator classes. -/
theorem toRows_surjective (h : ι → R) :
    Function.Surjective (toRows (R := R) (ι := ι) h) := by
  intro v
  refine ⟨∑ i : ι, v i • graphGeneratorClass
    (R := R) (ι := ι) h i, ?_⟩
  ext j
  simp [toRows_graphGeneratorClass]

/-- Zero translated linear row forces a graph-ideal element into `I_h²`. -/
theorem mem_graphIdeal_square_of_rows_eq_zero
    (h : ι → R)
    (x : GraphI (R := R) (ι := ι) h)
    (hx : graphLinearCoefficients (R := R) (ι := ι) h x = 0) :
    x.1 ∈ (graphIdeal h) ^ 2 := by
  have htranslatedRows :
      CoordinateCentreCotangentBasis.linearCoefficients
        (R := R) (ι := ι) (translatedElement h x) = 0 := by
    exact hx
  have htranslatedSquare :=
    CoordinateCentreCotangentBasis.mem_square_of_linearCoefficients_eq_zero
      (R := R) (ι := ι) (translatedElement h x) htranslatedRows
  have hback := Ideal.mem_map_of_mem (translate (-h)) htranslatedSquare
  rw [map_originIdeal_pow_eq_graphIdeal_pow] at hback
  have hvalue : translate (-h) (translate h x.1) = x.1 := by
    have hcomp := congrArg
      (fun H : P (R := R) (ι := ι) →ₐ[R] P => H x.1)
      (translate_neg_comp h)
    simpa [AlgHom.comp_apply] using hcomp
  simpa [translatedElement, hvalue] using hback

/-- The graph conormal coefficient map is injective. -/
theorem toRows_injective (h : ι → R) :
    Function.Injective (toRows (R := R) (ι := ι) h) := by
  rw [LinearMap.injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := (GraphI (R := R) (ι := ι) h).toCotangent_surjective z
  apply ((GraphI (R := R) (ι := ι) h).toCotangent_eq_zero x).mpr
  apply mem_graphIdeal_square_of_rows_eq_zero
  simpa [toRows] using hz

/-- Canonical free conormal basis of a polynomial graph centre. -/
noncomputable def cotangentEquivRows (h : ι → R) :
    (GraphI (R := R) (ι := ι) h).Cotangent ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofBijective
    (toRows (R := R) (ι := ι) h)
    ⟨toRows_injective (R := R) (ι := ι) h,
      toRows_surjective (R := R) (ι := ι) h⟩

end

end PolynomialGraphCentreCotangentBasis
end Experimental
end PCRLean
