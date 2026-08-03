import Mathlib
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import PCRLean.PolynomialFrobeniusExtraction

/-!
# Univariate Frobenius order heredity

For a polynomial over a field, the order at the origin is its trailing degree.
The zero polynomial is declared singular at every positive mark.  This file
proves that prime-power mark compression preserves the marked singular
condition exactly:

`ord_0(g^q) >= q*m  ↔  ord_0(g) >= m`.

After Taylor translation the same equivalence holds at every rational point.
Combining this with perfect-field Frobenius extraction proves that replacing a
derivative-zero marked equation `(f, p*m)` by its canonical root `(g,m)` does
not change its pointwise marked singular locus in the one-variable affine
model.

This is a genuine local heredity theorem for Frobenius presentation
normalization.  It does not yet prove the corresponding statement for general
differential Rees algebras, several variables, nonprincipal ideals, passive
owners, boundaries, or controlled blowup transforms.
-/

namespace PCRLean
namespace Experimental
namespace UnivariateFrobeniusOrderHeredity

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Marked singularity at the origin.  The zero polynomial has infinite order,
so it is included explicitly. -/
def AtOriginSingular (f : K[X]) (mark : Nat) : Prop :=
  f = 0 ∨ mark ≤ f.natTrailingDegree

/-- Marked singularity at a rational point, defined by Taylor translation. -/
def AtPointSingular (a : K) (f : K[X]) (mark : Nat) : Prop :=
  AtOriginSingular (Polynomial.taylor a f) mark

/-- Trailing order multiplies exactly under positive powers of a nonzero
polynomial. -/
theorem natTrailingDegree_pow
    (f : K[X]) (n : Nat) (hf : f ≠ 0) :
    (f ^ n).natTrailingDegree = n * f.natTrailingDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        Polynomial.natTrailingDegree_mul (pow_ne_zero n hf) hf,
        ih, Nat.succ_mul]

/-- Prime-power mark scaling preserves the singular condition at the origin. -/
theorem atOriginSingular_pow_iff
    (q mark : Nat) (hq : 0 < q) (g : K[X]) :
    AtOriginSingular (g ^ q) (q * mark) ↔
      AtOriginSingular g mark := by
  by_cases hg : g = 0
  · subst g
    simp [AtOriginSingular, hq.ne']
  · have hpow : g ^ q ≠ 0 := pow_ne_zero q hg
    simp only [AtOriginSingular, hg, hpow, false_or]
    rw [natTrailingDegree_pow g q hg]
    exact Nat.mul_le_mul_left_iff hq

/-- Frobenius compression preserves the singular condition at the origin. -/
theorem root_compression_atOrigin_iff
    (q mark : Nat) (hq : 0 < q)
    {f g : K[X]} (hroot : g ^ q = f) :
    AtOriginSingular f (q * mark) ↔
      AtOriginSingular g mark := by
  rw [← hroot]
  exact atOriginSingular_pow_iff q mark hq g

/-- Taylor translation commutes with powers, so the same order reflection holds
at every rational point. -/
theorem atPointSingular_pow_iff
    (q mark : Nat) (hq : 0 < q)
    (a : K) (g : K[X]) :
    AtPointSingular a (g ^ q) (q * mark) ↔
      AtPointSingular a g mark := by
  unfold AtPointSingular
  rw [Polynomial.taylor_pow]
  exact atOriginSingular_pow_iff q mark hq (Polynomial.taylor a g)

/-- Root compression preserves the marked singular condition at every rational
point. -/
theorem root_compression_atPoint_iff
    (q mark : Nat) (hq : 0 < q)
    (a : K) {f g : K[X]} (hroot : g ^ q = f) :
    AtPointSingular a f (q * mark) ↔
      AtPointSingular a g mark := by
  rw [← hroot]
  exact atPointSingular_pow_iff q mark hq a g

section Perfect

variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- For a derivative-zero equation over a perfect field, canonical Frobenius
root extraction preserves the marked singular condition at every rational
point. -/
theorem derivativeZero_root_preserves_atPoint
    (mark : Nat) (a : K) (f : K[X])
    (hderiv : Polynomial.derivative f = 0) :
    AtPointSingular a f (p * mark) ↔
      AtPointSingular a
        (PolynomialFrobeniusExtraction.frobeniusRoot p f) mark := by
  apply root_compression_atPoint_iff p mark (Fact.out : p.Prime).pos a
  exact PolynomialFrobeniusExtraction.frobeniusRoot_pow_eq p f hderiv

/-- The same perfect-field heredity statement at the origin. -/
theorem derivativeZero_root_preserves_atOrigin
    (mark : Nat) (f : K[X])
    (hderiv : Polynomial.derivative f = 0) :
    AtOriginSingular f (p * mark) ↔
      AtOriginSingular
        (PolynomialFrobeniusExtraction.frobeniusRoot p f) mark := by
  apply root_compression_atOrigin_iff p mark (Fact.out : p.Prime).pos
  exact PolynomialFrobeniusExtraction.frobeniusRoot_pow_eq p f hderiv

end Perfect

end

end UnivariateFrobeniusOrderHeredity
end Experimental
end PCRLean
