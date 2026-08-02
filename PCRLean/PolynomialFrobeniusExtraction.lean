import Mathlib
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Polynomial.Expand

/-!
# Frobenius extraction from vanishing derivative

Over a perfect field of characteristic `p`, a univariate polynomial with zero
formal derivative is a `p`th power.  The proof is constructive: contract the
exponents by `p` and apply the inverse Frobenius to the coefficients.

This is the one-variable algebraic core of the Frobenius-extraction dichotomy.
For a smooth `p`-basis chart the multivariate statement is obtained by applying
the same argument successively to every coordinate/Hasse direction.
-/

namespace PCRLean
namespace PolynomialFrobeniusExtraction

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- Contract exponents by `p` and take canonical coefficientwise Frobenius
roots. -/
def frobeniusRoot (f : K[X]) : K[X] :=
  (Polynomial.contract p f).map (frobeniusEquiv K p).symm.toRingHom

/-- Frobenius applied coefficientwise to the extracted root recovers the
contracted polynomial. -/
theorem map_frobenius_frobeniusRoot (f : K[X]) :
    (frobeniusRoot p f).map (frobenius K p) = Polynomial.contract p f := by
  rw [frobeniusRoot, Polynomial.map_map]
  convert Polynomial.map_id (Polynomial.contract p f) using 1
  ext a
  simp

/-- If the derivative vanishes, the canonical extracted root raises back to
`f`. -/
theorem frobeniusRoot_pow_eq
    (f : K[X]) (hf : Polynomial.derivative f = 0) :
    (frobeniusRoot p f) ^ p = f := by
  calc
    (frobeniusRoot p f) ^ p =
        (Polynomial.expand K p (frobeniusRoot p f)).map (frobenius K p) := by
          symm
          exact Polynomial.map_frobenius_expand (p := p) (frobeniusRoot p f)
    _ = Polynomial.expand K p
          ((frobeniusRoot p f).map (frobenius K p)) := by
          exact Polynomial.map_expand
    _ = Polynomial.expand K p (Polynomial.contract p f) := by
          rw [map_frobenius_frobeniusRoot]
    _ = f := Polynomial.expand_contract p hf (Fact.out.ne_zero)

/-- Vanishing derivative is therefore equivalent to being a `p`th power over
our perfect coefficient field. -/
theorem derivative_eq_zero_iff_exists_pow (f : K[X]) :
    Polynomial.derivative f = 0 ↔ ∃ g : K[X], g ^ p = f := by
  constructor
  · intro hf
    exact ⟨frobeniusRoot p f, frobeniusRoot_pow_eq p f hf⟩
  · rintro ⟨g, rfl⟩
    rw [Polynomial.derivative_pow]
    have hp : (p : K) = 0 := CharP.cast_eq_zero K p
    rw [hp]
    simp

/-- If `f` is not a `p`th power, its ordinary derivative is nonzero. -/
theorem derivative_ne_zero_of_not_pow
    (f : K[X]) (hnot : ¬ ∃ g : K[X], g ^ p = f) :
    Polynomial.derivative f ≠ 0 := by
  intro hf
  exact hnot ((derivative_eq_zero_iff_exists_pow p f).mp hf)

/-- The extracted root is unique in a reduced perfect field. -/
theorem frobeniusRoot_unique
    (f g : K[X]) (hg : g ^ p = f) :
    g = frobeniusRoot p f := by
  apply (Polynomial.map_injective
    (frobeniusEquiv K p).toRingHom.injective)
  have hmapg : g.map (frobenius K p) = g ^ p := by
    ext n
    simp [frobenius_def]
  rw [hmapg, hg, map_frobenius_frobeniusRoot]
  -- Both sides have only contracted `p`-multiple coefficients after the
  -- derivative-zero relation forced by `hg`.
  have hfzero : Polynomial.derivative f = 0 :=
    (derivative_eq_zero_iff_exists_pow p f).mpr ⟨g, hg⟩
  rw [← Polynomial.expand_inj (R := K) (Fact.out.pos)]
  rw [Polynomial.expand_contract p hfzero (Fact.out.ne_zero)]
  simp [Polynomial.map_expand]

end

end PolynomialFrobeniusExtraction
end PCRLean
