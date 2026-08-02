import Mathlib
import PCRLean.MarkedIdeal

namespace PCRLean
namespace QuasilinearSplit

universe u v

variable {R : Type u} {σ : Type v}
variable [CommRing R] [CharP R 2] [Fintype σ] [DecidableEq σ]

abbrev P := MvPolynomial σ R

private theorem natCast_two_eq_zero_poly :
    ((2 : Nat) : P) = 0 := by
  have hR : ((2 : Nat) : R) = 0 := CharP.cast_eq_zero R 2
  simpa only [map_zero] using
    congrArg (MvPolynomial.C : R → P) hR

/-- Frobenius additivity of the square map on the polynomial ring, derived
explicitly from characteristic two. -/
theorem add_sq (x y : P) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  calc
    (x + y) ^ 2 = x ^ 2 + ((2 : Nat) : P) * x * y + y ^ 2 := by ring
    _ = x ^ 2 + y ^ 2 := by rw [natCast_two_eq_zero_poly]; ring

/-- The square of a finite sum is the sum of the squares. -/
theorem finset_sum_sq (s : Finset σ) (f : σ → P) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, (f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, add_sq, ih]

/-- A linear Frobenius root with coefficients `b`. -/
def linearRoot (b : σ → R) : P :=
  ∑ i : σ, MvPolynomial.C (b i) * MvPolynomial.X i

/-- The associated split quasilinear quadratic form. -/
def quasilinearForm (b : σ → R) : P :=
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
def rootCentre (b : σ → R) : Ideal P :=
  Ideal.span {linearRoot b}

/-- The linear root belongs to its actual centre. -/
theorem linearRoot_mem_centre (b : σ → R) :
    linearRoot b ∈ rootCentre b :=
  Ideal.mem_span_singleton_self (linearRoot b)

/-- The quasilinear quadratic equation belongs to the square of the root
centre. -/
theorem quasilinear_mem_rootCentre_sq (b : σ → R) :
    quasilinearForm b ∈ rootCentre b ^ 2 := by
  rw [quasilinear_eq_root_square]
  exact Ideal.pow_mem_pow (linearRoot_mem_centre b) 2

/-- Therefore the principal mark-two quasilinear packet is permissible for the
actual split root centre. -/
theorem marked_quasilinear_permissible (b : σ → R) :
    MarkedIdeal.Permissible
      (R := P)
      ⟨Ideal.span {quasilinearForm b}, 2, by omega⟩
      (rootCentre b) := by
  exact MarkedIdeal.permissible_span_singleton (R := P) (by omega)
    (quasilinear_mem_rootCentre_sq b)

/-- The polar expression of the split square vanishes identically. -/
theorem polar_zero (b : σ → R) (x y : P) :
    ((linearRoot b + x + y) ^ 2 - (linearRoot b + x) ^ 2 -
      (linearRoot b + y) ^ 2 + (linearRoot b) ^ 2) = 0 := by
  repeat' rw [add_sq]
  ring

end QuasilinearSplit
end PCRLean
