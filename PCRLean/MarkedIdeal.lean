import Mathlib

namespace PCRLean
namespace MarkedIdeal

universe u

variable (R : Type u) [CommRing R]

/-- An affine marked ideal. This is the finite algebraic input used by the
explicit chamber proofs. -/
structure Packet where
  ideal : Ideal R
  mark : Nat
  mark_pos : 0 < mark

variable {R}

/-- A centre ideal is marked-permissible when the marked ideal is contained in
the corresponding power of the centre. -/
def Permissible (P : Packet R) (C : Ideal R) : Prop :=
  P.ideal ≤ C ^ P.mark

/-- A single equation lying in the marked power generates a permissible
principal marked ideal. -/
theorem permissible_span_singleton {f : R} {m : Nat} (hm : 0 < m)
    {C : Ideal R} (hf : f ∈ C ^ m) :
    Permissible (R := R) ⟨Ideal.span {f}, m, hm⟩ C := by
  rw [Permissible, Ideal.span_le]
  simpa using hf

/-- Permissibility is monotone when the centre ideal is enlarged. -/
theorem permissible_mono {P : Packet R} {C D : Ideal R}
    (hP : Permissible P C) (hCD : C ≤ D) : Permissible P D := by
  apply hP.trans
  gcongr

/-- A product of equations each lying in the appropriate centre powers lies in
the sum of the marks. -/
theorem mul_mem_pow_add {C : Ideal R} {f g : R} {m n : Nat}
    (hf : f ∈ C ^ m) (hg : g ∈ C ^ n) : f * g ∈ C ^ (m + n) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hf hg

/-- If an ideal is already contained in a marked centre power, adjoining more
generators inside that same power preserves permissibility. -/
theorem sup_permissible {I J C : Ideal R} {m : Nat}
    (hI : I ≤ C ^ m) (hJ : J ≤ C ^ m) : I ⊔ J ≤ C ^ m := by
  exact sup_le hI hJ

/-- Ordinary generator support is strictly weaker than marked-square
containment: `X` is in `(X)` but not in `(X^2)`. -/
theorem generator_support_not_square_span :
    Polynomial.X ∈ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℤ)) ∧
      Polynomial.X ∉ (Ideal.span {Polynomial.X ^ 2} : Ideal (Polynomial ℤ)) := by
  constructor
  · exact Ideal.mem_span_singleton_self Polynomial.X
  · rw [Ideal.mem_span_singleton]
    exact (Polynomial.monic_X.pow 2).not_dvd_of_natDegree_lt (by simp) (by simp)

end MarkedIdeal
end PCRLean
