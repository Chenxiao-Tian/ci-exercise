import Mathlib
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Polynomial.Expand

/-!
# Perfect-field Frobenius roots of derivative-zero polynomials

For a polynomial over a perfect field of positive characteristic, vanishing of
the ordinary derivative is equivalent to the existence of a polynomial
Frobenius root.  This is the one-variable algebraic core of the
full-exceptional-direction branch: if every transverse derivative vanishes,
the leading form is a pure Frobenius power rather than a new directional
obstruction.
-/

namespace PCRLean
namespace PolynomialFrobeniusRoot

noncomputable section

universe u

variable {K : Type u} (p : Nat)
variable [Field K] [ExpChar K p] [PerfectRing K p]

/-- Coefficientwise inverse Frobenius. -/
def rootCoeffs (f : K[X]) : K[X] :=
  f.map (frobeniusEquiv K p).symm.toRingEquiv.toRingHom

/-- Applying Frobenius to the rooted coefficients recovers the original
polynomial. -/
theorem map_frobenius_rootCoeffs (f : K[X]) :
    f.rootCoeffs p |>.map (frobenius K p) = f := by
  ext n
  simp [rootCoeffs]

/-- The canonical perfect-field root of a derivative-zero polynomial. -/
def frobeniusRoot (f : K[X]) : K[X] :=
  (Polynomial.contract p f).rootCoeffs p

/-- A derivative-zero polynomial is exactly the `p`-th power of its canonical
Frobenius root. -/
theorem frobeniusRoot_pow
    (hp : p ≠ 0) (f : K[X]) (hder : Polynomial.derivative f = 0) :
    (frobeniusRoot p f) ^ p = f := by
  have hexpand : Polynomial.expand K p (Polynomial.contract p f) = f := by
    exact Polynomial.expand_contract' (p := p) hder
  calc
    (frobeniusRoot p f) ^ p =
        (Polynomial.expand K p (frobeniusRoot p f)).map (frobenius K p) := by
      symm
      exact Polynomial.map_frobenius_expand (p := p) (frobeniusRoot p f)
    _ = Polynomial.expand K p
        ((frobeniusRoot p f).map (frobenius K p)) := by
      exact Polynomial.map_expand.symm
    _ = Polynomial.expand K p (Polynomial.contract p f) := by
      rw [frobeniusRoot, map_frobenius_rootCoeffs]
    _ = f := hexpand

/-- Every derivative-zero polynomial over a perfect field has a Frobenius
root. -/
theorem exists_pow_eq_of_derivative_eq_zero
    (hp : p ≠ 0) (f : K[X]) (hder : Polynomial.derivative f = 0) :
    ∃ g : K[X], g ^ p = f :=
  ⟨frobeniusRoot p f, frobeniusRoot_pow p hp f hder⟩

/-- Conversely every `p`-th power has zero derivative in positive
characteristic. -/
theorem derivative_pow_eq_zero (f : K[X]) :
    Polynomial.derivative (f ^ p) = 0 := by
  rw [Polynomial.derivative_pow]
  have hpzero : (p : K) = 0 := by
    exact ExpChar.cast_eq_zero K p
  rw [hpzero]
  simp

/-- The exact one-variable dichotomy. -/
theorem derivative_eq_zero_iff_exists_frobeniusRoot
    (hp : p ≠ 0) (f : K[X]) :
    Polynomial.derivative f = 0 ↔ ∃ g : K[X], g ^ p = f := by
  constructor
  · exact exists_pow_eq_of_derivative_eq_zero p hp f
  · rintro ⟨g, rfl⟩
    exact derivative_pow_eq_zero p g

end

end PolynomialFrobeniusRoot
end PCRLean
