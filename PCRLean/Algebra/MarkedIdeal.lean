import Mathlib
import PCRLean.Chambers.OddCusp

/-!
# Marked ideals and elementary permissibility certificates

This file begins the algebraic legality layer of the PCR formalization.  A
centre ideal `C` is permissible for a marked ideal `(J,b)` when `J ≤ C^b`.
The theorems below prove this containment for the explicit odd-cusp, tame
ramified-quadratic, and Artin-Schreier collision generators used by the local
chart programs.

The results are ideal-theoretic.  Regularity of a centre and boundary/passive
compatibility are separate certificates.
-/

namespace PCRLean.Algebra

/-- A marked ideal over a commutative ring. -/
structure MarkedIdeal (R : Type*) [CommRing R] where
  ideal : Ideal R
  mark : ℕ
  mark_pos : 0 < mark

namespace MarkedIdeal

variable {R : Type*} [CommRing R]

/-- Ideal-theoretic permissibility of a centre. -/
def Permissible (M : MarkedIdeal R) (C : Ideal R) : Prop :=
  M.ideal ≤ C ^ M.mark

end MarkedIdeal

variable {R : Type*} [CommRing R]

/-- If `x ∈ I`, then every power `x^n` lies in the corresponding ideal power. -/
theorem pow_mem_pow {I : Ideal R} {x : R} (hx : x ∈ I) :
    ∀ n : ℕ, x ^ n ∈ I ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact Submodule.smul_mem_smul (pow_mem_pow hx n) hx

/-- The product of two centre elements lies in the square of the centre ideal. -/
theorem mul_mem_square {I : Ideal R} {x y : R} (hx : x ∈ I) (hy : y ∈ I) :
    x * y ∈ I ^ 2 := by
  rw [pow_two]
  exact Submodule.smul_mem_smul hx hy

/-- In particular a square of a centre element lies in the centre square. -/
theorem square_mem_square {I : Ideal R} {x : R} (hx : x ∈ I) :
    x ^ 2 ∈ I ^ 2 := by
  simpa [pow_two] using mul_mem_square hx hx

/-- Every power whose exponent is at least two lies in the centre square. -/
theorem pow_add_two_mem_square {I : Ideal R} {x : R} (hx : x ∈ I) (n : ℕ) :
    x ^ (n + 2) ∈ I ^ 2 := by
  rw [pow_add]
  exact (I ^ 2).mul_mem_left (x ^ n) (square_mem_square hx)

/-- A singleton generator contained in an ideal generates a subideal. -/
theorem span_singleton_le_of_mem {J : Ideal R} {f : R} (hf : f ∈ J) :
    Ideal.span ({f} : Set R) ≤ J := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  have hxf : x = f := by simpa using hx
  simpa [hxf] using hf

/-- The coordinate point/axis ideal containing `s` and `y` is mark-two
permissible for every nonterminal odd cusp `y^2+s^(2(n+1)+1)`. -/
theorem oddCusp_generator_mem_square {I : Ideal R} {s y : R}
    (hs : s ∈ I) (hy : y ∈ I) (n : ℕ) :
    y ^ 2 + s ^ PCRLean.Chambers.OddCusp.oddExp (n + 1) ∈ I ^ 2 := by
  apply (I ^ 2).add_mem (square_mem_square hy)
  rw [PCRLean.Chambers.OddCusp.oddExp_succ]
  exact pow_add_two_mem_square hs (PCRLean.Chambers.OddCusp.oddExp n)

/-- Principal marked-ideal form of odd-cusp permissibility. -/
theorem oddCusp_principal_permissible {I : Ideal R} {s y : R}
    (hs : s ∈ I) (hy : y ∈ I) (n : ℕ) :
    Ideal.span ({y ^ 2 + s ^ PCRLean.Chambers.OddCusp.oddExp (n + 1)} : Set R) ≤ I ^ 2 :=
  span_singleton_le_of_mem (oddCusp_generator_mem_square hs hy n)

/-- The collision centre containing `t` and `z` is mark-two permissible for
the tame ramified generator `z^2-u*t^(n+2)`. -/
theorem ramifiedQuadratic_generator_mem_square {I : Ideal R} {t z u : R}
    (ht : t ∈ I) (hz : z ∈ I) (n : ℕ) :
    z ^ 2 - u * t ^ (n + 2) ∈ I ^ 2 := by
  apply (I ^ 2).sub_mem (square_mem_square hz)
  exact (I ^ 2).mul_mem_left u (pow_add_two_mem_square ht n)

/-- Principal marked-ideal form of tame ramified collision permissibility. -/
theorem ramifiedQuadratic_principal_permissible {I : Ideal R} {t z u : R}
    (ht : t ∈ I) (hz : z ∈ I) (n : ℕ) :
    Ideal.span ({z ^ 2 - u * t ^ (n + 2)} : Set R) ≤ I ^ 2 :=
  span_singleton_le_of_mem (ramifiedQuadratic_generator_mem_square ht hz n)

/-- The collision centre containing `t` and `z` is mark-two permissible for
the Artin-Schreier generator at an active collision stage. -/
theorem artinSchreier_generator_mem_square {I : Ideal R} {t z u : R}
    (ht : t ∈ I) (hz : z ∈ I) (m r : ℕ) :
    z ^ 2 + t ^ (m + 1) * z + u * t ^ (r + 2) ∈ I ^ 2 := by
  have htm : t ^ (m + 1) ∈ I := by
    rw [pow_succ]
    exact I.mul_mem_left (t ^ m) ht
  have hcross : t ^ (m + 1) * z ∈ I ^ 2 :=
    mul_mem_square htm hz
  have htail : u * t ^ (r + 2) ∈ I ^ 2 :=
    (I ^ 2).mul_mem_left u (pow_add_two_mem_square ht r)
  exact (I ^ 2).add_mem ((I ^ 2).add_mem (square_mem_square hz) hcross) htail

/-- Principal marked-ideal form of Artin-Schreier collision permissibility. -/
theorem artinSchreier_principal_permissible {I : Ideal R} {t z u : R}
    (ht : t ∈ I) (hz : z ∈ I) (m r : ℕ) :
    Ideal.span ({z ^ 2 + t ^ (m + 1) * z + u * t ^ (r + 2)} : Set R) ≤ I ^ 2 :=
  span_singleton_le_of_mem (artinSchreier_generator_mem_square ht hz m r)

end PCRLean.Algebra
