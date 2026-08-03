import Mathlib
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity

/-!
# Cotangent basis of a coordinate centre

Let `I = (Z_i)` be the full variable ideal in `R[Z_i]`.  The conormal module
`I / I^2` is canonically the free module of coefficient rows `ι → R`: the class
of `Z_i` is the `i`-th standard basis vector.

The proof uses the exact monomial criterion for powers of the variable ideal.
A polynomial in `I` has zero class in `I/I^2` exactly when all of its degree-one
coefficients vanish.  This gives both an explicit inverse and injectivity.

This is the missing regular-immersion component of the coordinate local model.
Transport to polynomial graph centres and scheme-level gluing are separate.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateCentreCotangentBasis

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

abbrev P := MvPolynomial ι R
abbrev I : Ideal (P (R := R) (ι := ι)) :=
  ReducedPolynomialGraphCentreHeredity.originIdeal (R := R) (ι := ι)

/-- Degree-one coefficients of an element of the coordinate ideal. -/
def linearCoefficients :
    I (R := R) (ι := ι) →ₗ[R] (ι → R) where
  toFun x i := MvPolynomial.coeff (Finsupp.single i 1) x.1
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro r x
    ext i
    simp [Algebra.smul_def]

/-- Products of two centre equations have no degree-one coefficient. -/
theorem linearCoefficients_mul_zero
    (x y : I (R := R) (ι := ι)) :
    linearCoefficients (R := R) (ι := ι) (x * y) = 0 := by
  ext i
  change MvPolynomial.coeff (Finsupp.single i 1) (x.1 * y.1) = 0
  have hxy : x.1 * y.1 ∈
      (MvPolynomial.idealOfVars ι R) ^ 2 := by
    simpa [pow_two] using (Ideal.mul_mem_mul x.2 y.2)
  have hdegree :=
    (MvPolynomial.mem_pow_idealOfVars_iff 2 (x.1 * y.1)).mp hxy
  by_contra hcoeff
  have hsupp : Finsupp.single i 1 ∈ (x.1 * y.1).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hbound := hdegree (Finsupp.single i 1) hsupp
  simpa using hbound

/-- The coefficient-row map on the conormal module. -/
def toRows :
    (I (R := R) (ι := ι)).Cotangent →ₗ[R] (ι → R) :=
  Ideal.Cotangent.lift
    (linearCoefficients (R := R) (ι := ι))
    (linearCoefficients_mul_zero (R := R) (ι := ι))

/-- Class of one coordinate generator in `I/I²`. -/
def variableClass (i : ι) : (I (R := R) (ι := ι)).Cotangent :=
  (I (R := R) (ι := ι)).toCotangent
    ⟨MvPolynomial.X i, Ideal.subset_span ⟨i, rfl⟩⟩

@[simp] theorem toRows_variableClass (i j : ι) :
    toRows (R := R) (ι := ι) (variableClass (R := R) (ι := ι) i) j =
      if j = i then 1 else 0 := by
  simp [toRows, variableClass, linearCoefficients]

/-- Every coefficient row is represented by the corresponding linear
combination of coordinate classes. -/
theorem toRows_surjective :
    Function.Surjective (toRows (R := R) (ι := ι)) := by
  intro v
  refine ⟨∑ i : ι, v i • variableClass (R := R) (ι := ι) i, ?_⟩
  ext j
  simp [toRows_variableClass]

/-- Vanishing of all degree-one coefficients forces an element of `I` into
`I²`. -/
theorem mem_square_of_linearCoefficients_eq_zero
    (x : I (R := R) (ι := ι))
    (hx : linearCoefficients (R := R) (ι := ι) x = 0) :
    x.1 ∈ (MvPolynomial.idealOfVars ι R) ^ 2 := by
  apply (MvPolynomial.mem_pow_idealOfVars_iff 2 x.1).mpr
  intro d hd
  have hdegreeOne :=
    (MvPolynomial.mem_pow_idealOfVars_iff 1 x.1).mp x.2 d hd
  by_contra hnot
  have hlt : Finsupp.degree d < 2 := Nat.lt_of_not_ge hnot
  have hdeg : Finsupp.degree d = 1 := by omega
  have hrange :
      d ∈ Set.range (fun i : ι => Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hdeg
  rcases hrange with ⟨i, rfl⟩
  have hrow :
      MvPolynomial.coeff (Finsupp.single i 1) x.1 = 0 := by
    have hi := congrFun hx i
    simpa [linearCoefficients] using hi
  exact (MvPolynomial.mem_support_iff.mp hd) hrow

/-- The coefficient-row map is injective. -/
theorem toRows_injective :
    Function.Injective (toRows (R := R) (ι := ι)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := (I (R := R) (ι := ι)).toCotangent_surjective z
  apply ((I (R := R) (ι := ι)).toCotangent_eq_zero x).mpr
  apply mem_square_of_linearCoefficients_eq_zero
  simpa [toRows] using hz

/-- Canonical free conormal basis for the coordinate centre. -/
noncomputable def cotangentEquivRows :
    (I (R := R) (ι := ι)).Cotangent ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofBijective
    (toRows (R := R) (ι := ι))
    ⟨toRows_injective (R := R) (ι := ι),
      toRows_surjective (R := R) (ι := ι)⟩

end

end CoordinateCentreCotangentBasis
end Experimental
end PCRLean
