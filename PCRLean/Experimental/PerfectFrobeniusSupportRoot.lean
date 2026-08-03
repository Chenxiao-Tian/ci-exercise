import Mathlib
import PCRLean.Experimental.PerfectFrobeniusRankZeroEscape
import PCRLean.Experimental.FrobeniusRootDegreeDescent

/-!
# Experimental perfect-field roots from support divisibility

Let `K` be perfect of characteristic `p`.  If every exponent in every monomial
of a polynomial is divisible by `p^e`, divide all exponents by `p^e` and apply
iterated inverse Frobenius to every coefficient.  The resulting explicitly
constructed polynomial has `p^e`-th power equal to the original polynomial.

This is a general Frobenius-root theorem, not restricted to pure linear forms.
For `e > 0` and a nonconstant root, total degree strictly decreases.  Hence
repeated extraction from the Frobenius image is well founded.

The remaining differential bridge is to prove that the relevant rank-zero
Hasse conditions force the support-divisibility predicate.  Imperfect fields
require a radicial coefficient extension and descent.
-/

namespace PCRLean
namespace Experimental
namespace PerfectFrobeniusSupportRoot

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

/-- Divide every monomial exponent by a positive integer. -/
def divideExponent (q : Nat) (d : σ →₀ Nat) : σ →₀ Nat :=
  d.mapRange (fun n => n / q) (by simp)

/-- Every exponent appearing in the support is divisible by `p^e`. -/
def ExponentDivisible (e : Nat) (f : MvPolynomial σ K) : Prop :=
  ∀ d ∈ f.support, ∀ i, p ^ e ∣ d i

/-- Scaling the divided exponent recovers the original exponent vector. -/
theorem smul_divideExponent_eq
    (q : Nat) (hq : 0 < q)
    (d : σ →₀ Nat) (hdiv : ∀ i, q ∣ d i) :
    q • divideExponent q d = d := by
  ext i
  simp [divideExponent, Nat.mul_div_cancel' (hdiv i)]

/-- Explicit coefficient-and-support Frobenius root. -/
def rootPolynomial (e : Nat) (f : MvPolynomial σ K) :
    MvPolynomial σ K :=
  ∑ d in f.support,
    MvPolynomial.monomial (divideExponent (p ^ e) d)
      (PerfectFrobeniusRankZeroEscape.frobeniusRootIter p e
        (MvPolynomial.coeff d f))

/-- One rooted monomial recovers the original monomial after `p^e`-th power. -/
theorem monomial_root_pow
    (e : Nat) (d : σ →₀ Nat) (a : K)
    (hdiv : ∀ i, p ^ e ∣ d i) :
    (MvPolynomial.monomial (divideExponent (p ^ e) d)
      (PerfectFrobeniusRankZeroEscape.frobeniusRootIter p e a)) ^ (p ^ e) =
        MvPolynomial.monomial d a := by
  rw [MvPolynomial.monomial_pow]
  rw [PerfectFrobeniusRankZeroEscape.frobeniusRootIter_pow]
  rw [smul_divideExponent_eq]
  · rfl
  · exact pow_pos (Fact.out : p.Prime).pos e
  · exact hdiv

/-- Main explicit root theorem. -/
theorem rootPolynomial_pow
    (e : Nat) (f : MvPolynomial σ K)
    (hdiv : ExponentDivisible p e f) :
    (rootPolynomial p e f) ^ (p ^ e) = f := by
  classical
  rw [rootPolynomial]
  rw [PerfectFrobeniusRankZeroEscape.finset_sum_pow_char_pow
    p f.support
    (fun d => MvPolynomial.monomial (divideExponent (p ^ e) d)
      (PerfectFrobeniusRankZeroEscape.frobeniusRootIter p e
        (MvPolynomial.coeff d f))) e]
  calc
    (∑ d in f.support,
      (MvPolynomial.monomial (divideExponent (p ^ e) d)
        (PerfectFrobeniusRankZeroEscape.frobeniusRootIter p e
          (MvPolynomial.coeff d f))) ^ (p ^ e)) =
      ∑ d in f.support,
        MvPolynomial.monomial d (MvPolynomial.coeff d f) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact monomial_root_pow p e d _ (hdiv d hd)
    _ = f := MvPolynomial.sum_monomial_coeff f

/-- A support-divisible polynomial is explicitly a `p^e`-th power. -/
theorem exists_root
    (e : Nat) (f : MvPolynomial σ K)
    (hdiv : ExponentDivisible p e f) :
    ∃ g : MvPolynomial σ K, g ^ (p ^ e) = f :=
  ⟨rootPolynomial p e f, rootPolynomial_pow p e f hdiv⟩

/-- The explicit root of a nonzero polynomial is nonzero. -/
theorem rootPolynomial_ne_zero
    (e : Nat) (f : MvPolynomial σ K)
    (hdiv : ExponentDivisible p e f) (hf : f ≠ 0) :
    rootPolynomial p e f ≠ 0 := by
  intro hzero
  apply hf
  rw [← rootPolynomial_pow p e f hdiv, hzero]
  simp [pow_pos (Fact.out : p.Prime).pos e]

/-- If the explicit root has positive degree and `e > 0`, root extraction
strictly lowers total degree. -/
theorem rootPolynomial_totalDegree_lt
    (e : Nat) (he : 0 < e)
    (f : MvPolynomial σ K)
    (hdiv : ExponentDivisible p e f)
    (hroot : 0 < (rootPolynomial p e f).totalDegree) :
    (rootPolynomial p e f).totalDegree < f.totalDegree := by
  rw [← rootPolynomial_pow p e f hdiv]
  exact FrobeniusRootDegreeDescent.iteratedRoot_totalDegree_lt
    p e he _ hroot

/-- Support divisibility at a higher level implies divisibility at every lower
level. -/
theorem exponentDivisible_mono
    {e d : Nat} (hde : d ≤ e)
    {f : MvPolynomial σ K}
    (hdiv : ExponentDivisible p e f) :
    ExponentDivisible p d f := by
  intro m hm i
  rcases hdiv m hm i with ⟨c, hc⟩
  refine ⟨p ^ (e - d) * c, ?_⟩
  rw [← hc, ← pow_add]
  congr 1
  omega

end

end PerfectFrobeniusSupportRoot
end Experimental
end PCRLean
