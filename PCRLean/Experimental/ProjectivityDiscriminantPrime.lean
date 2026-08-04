import Mathlib

/-!
# Prime-product support for projectivity discriminants

For a prime ideal `P`, containment of a product ideal in `P` is equivalent to
containment of one of the two factors.

This is the prime-level algebra used in the proposed finite-module
projectivity discriminant

`Delta_r(M) = Fitt_r(M) * Ann(Fitt_{r-1}(M))`.

Combining this file with the standard Fitting criterion and the finite
annihilator localization lemma should identify `D(Delta_r(M))` with the
rank-`r` free locus.  That full module theorem remains a separate edge.
-/

namespace PCRLean
namespace Experimental
namespace ProjectivityDiscriminantPrime

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Product containment in a prime ideal. -/
theorem mul_le_prime_iff
    (P : Ideal R) (hP : P.IsPrime) (I J : Ideal R) :
    I * J ≤ P ↔ I ≤ P ∨ J ≤ P := by
  constructor
  · intro hmul
    by_cases hI : I ≤ P
    · exact Or.inl hI
    · by_cases hJ : J ≤ P
      · exact Or.inr hJ
      · obtain ⟨i, hiI, hiP⟩ := SetLike.not_le_iff_exists.mp hI
        obtain ⟨j, hjJ, hjP⟩ := SetLike.not_le_iff_exists.mp hJ
        have hij : i * j ∈ P := hmul (Ideal.mul_mem_mul hiI hjJ)
        exact (hP.mem_or_mem hij).elim hiP hjP
  · rintro (hI | hJ)
    · rw [Ideal.mul_le]
      intro i hi j hj
      exact P.mul_mem_right j (hI hi)
    · rw [Ideal.mul_le]
      intro i hi j hj
      exact P.mul_mem_left i (hJ hj)

/-- Complementary form: a prime avoids the product exactly when it avoids both
factors. -/
theorem not_mul_le_prime_iff
    (P : Ideal R) (hP : P.IsPrime) (I J : Ideal R) :
    ¬ I * J ≤ P ↔ (¬ I ≤ P ∧ ¬ J ≤ P) := by
  rw [mul_le_prime_iff P hP I J]
  tauto

end

end ProjectivityDiscriminantPrime
end Experimental
end PCRLean
