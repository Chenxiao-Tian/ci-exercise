import Mathlib

namespace PCRLean
namespace MarkedIdeal

universe u

variable (R : Type u) [CommRing R]

/-- An affine marked ideal.  This is the finite algebraic input used by the
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
  intro x hx
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  exact (C ^ m).mul_mem_left a hf

/-- Permissibility is monotone when the centre ideal is enlarged. -/
theorem permissible_mono {P : Packet R} {C D : Ideal R}
    (hP : Permissible P C) (hCD : C ≤ D) : Permissible P D := by
  intro x hx
  exact (Ideal.pow_le_pow_right hCD P.mark) (hP hx)

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

/-- Controlled transforms are never inferred merely from radical containment:
ordinary containment in a radical is weaker than containment in the marked
power.  The following concrete witness records this distinction. -/
theorem radical_support_not_marked_power :
    let C : Ideal (Polynomial ℤ) := Ideal.span {Polynomial.X}
    Polynomial.X ∈ C.radical ∧ Polynomial.X ∉ C ^ 2 := by
  dsimp
  constructor
  · exact Ideal.subset_radical (Ideal.subset_span (Set.mem_singleton _))
  · intro h
    have hdeg := Polynomial.natDegree_le_of_dvd
      (show Polynomial.X ^ 2 ∣ Polynomial.X from by
        simpa [Ideal.mem_span_singleton, pow_two] using h)
    norm_num at hdeg

end MarkedIdeal
end PCRLean
