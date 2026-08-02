import Mathlib
import Mathlib.FieldTheory.Perfect
import PCRLean.MarkedIdeal

namespace PCRLean
namespace QuasilinearSplit

universe u v

variable {R : Type u} {σ : Type v}
variable [CommRing R] [CharP R 2] [Fintype σ] [DecidableEq σ]

private theorem natCast_two_eq_zero_poly :
    ((2 : Nat) : MvPolynomial σ R) = 0 := by
  have hR : ((2 : Nat) : R) = 0 := CharP.cast_eq_zero R 2
  simpa only [map_zero] using
    congrArg (MvPolynomial.C : R → MvPolynomial σ R) hR

/-- Frobenius additivity of the square map on the polynomial ring. -/
theorem add_sq (x y : MvPolynomial σ R) :
    (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  calc
    (x + y) ^ 2 = x ^ 2 + ((2 : Nat) : MvPolynomial σ R) * x * y + y ^ 2 := by ring
    _ = x ^ 2 + y ^ 2 := by rw [natCast_two_eq_zero_poly]; ring

/-- The square of a finite sum is the sum of the squares. -/
theorem finset_sum_sq (s : Finset σ) (f : σ → MvPolynomial σ R) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, (f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, add_sq, ih]

/-- A linear Frobenius root with coefficients `b`. -/
def linearRoot (b : σ → R) : MvPolynomial σ R :=
  ∑ i : σ, MvPolynomial.C (b i) * MvPolynomial.X i

/-- The associated split quasilinear quadratic form. -/
def quasilinearForm (b : σ → R) : MvPolynomial σ R :=
  ∑ i : σ, MvPolynomial.C ((b i) ^ 2) * (MvPolynomial.X i) ^ 2

/-- Exact split-quasilinear identity: the full quadratic form is one square. -/
theorem quasilinear_eq_root_square (b : σ → R) :
    quasilinearForm b = (linearRoot b) ^ 2 := by
  classical
  rw [linearRoot, quasilinearForm, finset_sum_sq]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_pow]

/-- The actual root hyperplane ideal. -/
def rootCentre (b : σ → R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {linearRoot b}

/-- The linear root belongs to its actual centre. -/
theorem linearRoot_mem_centre (b : σ → R) :
    linearRoot b ∈ rootCentre b :=
  Ideal.mem_span_singleton_self (linearRoot b)

/-- The quasilinear quadratic equation belongs to the square of the root centre. -/
theorem quasilinear_mem_rootCentre_sq (b : σ → R) :
    quasilinearForm b ∈ rootCentre b ^ 2 := by
  rw [quasilinear_eq_root_square]
  exact Ideal.pow_mem_pow (linearRoot_mem_centre b) 2

/-- Therefore the principal mark-two quasilinear packet is permissible. -/
theorem marked_quasilinear_permissible (b : σ → R) :
    MarkedIdeal.Permissible
      (R := MvPolynomial σ R)
      ⟨Ideal.span {quasilinearForm b}, 2, by omega⟩
      (rootCentre b) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := MvPolynomial σ R) (by omega) (quasilinear_mem_rootCentre_sq b)

/-- The polar expression of the split square vanishes identically. -/
theorem polar_zero (b : σ → R) (x y : MvPolynomial σ R) :
    ((linearRoot b + x + y) ^ 2 - (linearRoot b + x) ^ 2 -
      (linearRoot b + y) ^ 2 + (linearRoot b) ^ 2) = 0 := by
  rw [add_sq (linearRoot b + x) y, add_sq (linearRoot b) x,
    add_sq (linearRoot b) x, add_sq (linearRoot b) y]
  ring

section Perfect

variable [PerfectRing R 2]

/-- The canonical coefficientwise square root supplied by perfection. -/
noncomputable def canonicalRootCoeff (a : σ → R) (i : σ) : R :=
  (frobeniusEquiv R 2).symm (a i)

/-- The canonical coefficient root squares back to the original coefficient. -/
theorem canonicalRootCoeff_sq (a : σ → R) (i : σ) :
    (canonicalRootCoeff a i) ^ 2 = a i := by
  exact frobeniusEquiv_symm_pow_p R 2 (a i)

/-- A general diagonal quasilinear quadratic form with coefficients `a`. -/
def diagonalForm (a : σ → R) : MvPolynomial σ R :=
  ∑ i : σ, MvPolynomial.C (a i) * (MvPolynomial.X i) ^ 2

/-- Its canonical linear root over a perfect characteristic-two ring. -/
noncomputable def canonicalLinearRoot (a : σ → R) : MvPolynomial σ R :=
  linearRoot (canonicalRootCoeff a)

/-- Every diagonal fully quasilinear quadratic form over a perfect
characteristic-two ring is the square of its canonical linear root. -/
theorem diagonalForm_eq_canonicalRoot_square (a : σ → R) :
    diagonalForm a = (canonicalLinearRoot a) ^ 2 := by
  rw [canonicalLinearRoot, ← quasilinear_eq_root_square]
  classical
  rw [diagonalForm, quasilinearForm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [canonicalRootCoeff_sq]

/-- The canonical actual root centre for a diagonal quasilinear form. -/
noncomputable def canonicalRootCentre (a : σ → R) : Ideal (MvPolynomial σ R) :=
  rootCentre (canonicalRootCoeff a)

/-- The diagonal quasilinear equation belongs to the square of its canonical
actual root centre. -/
theorem diagonalForm_mem_canonicalRootCentre_sq (a : σ → R) :
    diagonalForm a ∈ canonicalRootCentre a ^ 2 := by
  rw [diagonalForm_eq_canonicalRoot_square]
  exact Ideal.pow_mem_pow (linearRoot_mem_centre (canonicalRootCoeff a)) 2

/-- Hence the diagonal fully quasilinear mark-two packet is permissible. -/
theorem marked_diagonal_permissible (a : σ → R) :
    MarkedIdeal.Permissible
      (R := MvPolynomial σ R)
      ⟨Ideal.span {diagonalForm a}, 2, by omega⟩
      (canonicalRootCentre a) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := MvPolynomial σ R) (by omega)
    (diagonalForm_mem_canonicalRootCentre_sq a)

/-- The canonical coefficient root is unique. -/
theorem canonicalRootCoeff_unique (a : σ → R) (i : σ) {b : R}
    (hb : b ^ 2 = a i) : b = canonicalRootCoeff a i := by
  apply (frobeniusEquiv R 2).injective
  simpa [canonicalRootCoeff] using hb

end Perfect

end QuasilinearSplit
end PCRLean
