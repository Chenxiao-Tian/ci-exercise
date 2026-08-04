import Mathlib
import PCRLean.Experimental.ProjectivityDiscriminantPrime

/-!
# Finite products of joint-defect ideals

A finite family of coherent vanishing gates can be fused by multiplying their
ideals.  At a prime ideal, the product is contained in the prime exactly when
one factor is contained in it.  Equivalently, the principal-open complement of
the product is the simultaneous good locus of all factors.

This is the finite algebraic skeleton behind the joint-defect discriminant.  It
does not construct cotangent, Rees--Serre, boundary, passive, or contact
obstruction ideals.
-/

namespace PCRLean
namespace Experimental
namespace FiniteGateProductPrime

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- A finite product lies in a prime ideal exactly when at least one factor lies
in that prime. -/
theorem prod_le_prime_iff
    (P : Ideal R) (hP : P.IsPrime)
    (s : Finset ι) (F : ι → Ideal R) :
    (∏ i in s, F i) ≤ P ↔ ∃ i ∈ s, F i ≤ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [hP.ne_top]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rw [ProjectivityDiscriminantPrime.mul_le_prime_iff P hP]
      simp [ih, ha]

/-- Complementary form: the prime avoids the product exactly when it avoids
every individual gate ideal. -/
theorem not_prod_le_prime_iff
    (P : Ideal R) (hP : P.IsPrime)
    (s : Finset ι) (F : ι → Ideal R) :
    ¬ (∏ i in s, F i) ≤ P ↔
      ∀ i ∈ s, ¬ F i ≤ P := by
  rw [prod_le_prime_iff P hP s F]
  constructor
  · intro h i hi hFi
    exact h ⟨i, hi, hFi⟩
  · intro h hex
    rcases hex with ⟨i, hi, hFi⟩
    exact h i hi hFi

end

end FiniteGateProductPrime
end Experimental
end PCRLean
