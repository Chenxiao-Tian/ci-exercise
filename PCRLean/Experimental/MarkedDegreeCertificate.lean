import Mathlib
import PCRLean.MarkedIdeal

/-!
# Experimental marked-degree certificate

If generators `z` and `t` belong to one actual centre ideal `C`, then a mixed
term `z^a * t^b` belongs to `C^(a+b)`.  Since ideal powers decrease with the
exponent, any lower mark `d <= a+b` is also controlled.

This finite degree certificate unifies the local marked-containment checks in
odd cusps, tame quadratics, Artin--Schreier chambers, and hybrid Frobenius-root
examples.  It proves only marked-power membership, not regularity or transform
closure.
-/

namespace PCRLean
namespace Experimental
namespace MarkedDegreeCertificate

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Powers of an ideal are antitone in the exponent. -/
theorem pow_le_pow_of_le
    (C : Ideal R) {d n : Nat} (hdn : d ≤ n) :
    C ^ n ≤ C ^ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdn
  rw [pow_add, mul_comm]
  exact Ideal.mul_le_left

/-- A two-generator mixed monomial is controlled at its total selected degree. -/
theorem mixedMonomial_mem_total_pow
    {C : Ideal R} {z t : R} {a b : Nat}
    (hz : z ∈ C) (ht : t ∈ C) :
    z ^ a * t ^ b ∈ C ^ (a + b) := by
  exact MarkedIdeal.mul_mem_pow_add
    (Ideal.pow_mem_pow hz a)
    (Ideal.pow_mem_pow ht b)

/-- A mixed monomial whose selected total degree is at least the mark lies in
that marked power. -/
theorem mixedMonomial_mem_marked_pow
    {C : Ideal R} {z t : R} {a b d : Nat}
    (hz : z ∈ C) (ht : t ∈ C)
    (hdegree : d ≤ a + b) :
    z ^ a * t ^ b ∈ C ^ d := by
  exact pow_le_pow_of_le C hdegree
    (mixedMonomial_mem_total_pow hz ht)

/-- Multiplication by an arbitrary coefficient does not change the selected
marked degree. -/
theorem coefficient_mul_mixedMonomial_mem_marked_pow
    {C : Ideal R} {u z t : R} {a b d : Nat}
    (hz : z ∈ C) (ht : t ∈ C)
    (hdegree : d ≤ a + b) :
    u * (z ^ a * t ^ b) ∈ C ^ d := by
  exact (C ^ d).mul_mem_left u
    (mixedMonomial_mem_marked_pow hz ht hdegree)

/-- Pure selected powers are the one-generator specialization. -/
theorem purePower_mem_marked_pow
    {C : Ideal R} {z : R} {a d : Nat}
    (hz : z ∈ C) (hdegree : d ≤ a) :
    z ^ a ∈ C ^ d := by
  have htotal : z ^ a * (1 : R) ^ 0 ∈ C ^ d := by
    exact mixedMonomial_mem_marked_pow hz C.one_mem_top
      (by simpa using hdegree)
  simpa using htotal

/-- Tame quadratic template: `z^2-u*t^N` is mark-two controlled by `(z,t)` as
soon as `2 <= N`. -/
theorem tameQuadratic_mem_square
    {C : Ideal R} {z t u : R} {N : Nat}
    (hz : z ∈ C) (ht : t ∈ C) (hN : 2 ≤ N) :
    z ^ 2 - u * t ^ N ∈ C ^ 2 := by
  exact (C ^ 2).sub_mem
    (Ideal.pow_mem_pow hz 2)
    (by
      have htN : t ^ N ∈ C ^ 2 :=
        purePower_mem_marked_pow ht hN
      exact (C ^ 2).mul_mem_left u htN)

/-- Artin--Schreier quadratic template: every term of
`z^2 + t^m*z + u*t^r` is mark-two controlled by `(z,t)` when `m+1 >= 2` and
`r >= 2`. -/
theorem artinSchreierQuadratic_mem_square
    {C : Ideal R} {z t u : R} {m r : Nat}
    (hz : z ∈ C) (ht : t ∈ C)
    (hm : 2 ≤ m + 1) (hr : 2 ≤ r) :
    z ^ 2 + t ^ m * z + u * t ^ r ∈ C ^ 2 := by
  have hz2 : z ^ 2 ∈ C ^ 2 := Ideal.pow_mem_pow hz 2
  have htz : t ^ m * z ∈ C ^ 2 := by
    simpa [pow_one] using
      (mixedMonomial_mem_marked_pow ht hz hm :
        t ^ m * z ^ 1 ∈ C ^ 2)
  have htr : u * t ^ r ∈ C ^ 2 := by
    exact (C ^ 2).mul_mem_left u
      (purePower_mem_marked_pow ht hr)
  exact (C ^ 2).add_mem ((C ^ 2).add_mem hz2 htz) htr

end

end MarkedDegreeCertificate
end Experimental
end PCRLean
