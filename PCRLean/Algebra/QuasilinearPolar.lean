import Mathlib
import Mathlib.Algebra.CharP.Lemmas

/-!
# Quasilinear Frobenius forms have zero polar map

Progress 283 targets the fully quasilinear chamber.  The basic structural
fact is that a `p^e`-power form is additive in characteristic `p`; hence its
polar map is identically zero.  This file kernel-checks that fact both in one
variable and for diagonal finite-dimensional Frobenius forms.

It is a no-go for any algorithm that tries to recover a regular core from the
polar map alone.  It is not an existence theorem for the missing radicial
core.
-/

namespace PCRLean.Algebra.QuasilinearPolar

variable {R : Type*} [CommRing R]

/-- The homogeneous Frobenius monomial of height `e`. -/
def frobeniusForm (p e : ℕ) (x : R) : R :=
  x ^ (p ^ e)

/-- Polarization of a function vanishing at the origin. -/
def polar (q : R → R) (x y : R) : R :=
  q (x + y) - q x - q y

variable (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Frobenius powers are additive. -/
theorem frobenius_additive (e : ℕ) (x y : R) :
    frobeniusForm p e (x + y) =
      frobeniusForm p e x + frobeniusForm p e y := by
  simpa [frobeniusForm] using add_pow_char_pow x y p e

/-- Every pure Frobenius form has identically zero polar map. -/
theorem frobenius_polar_zero (e : ℕ) (x y : R) :
    polar (frobeniusForm p e) x y = 0 := by
  rw [polar, frobenius_additive]
  ring

/-- A scalar multiple of a pure Frobenius form still has zero polar map. -/
theorem scalar_frobenius_polar_zero (a : R) (e : ℕ) (x y : R) :
    polar (fun z => a * frobeniusForm p e z) x y = 0 := by
  rw [polar, frobenius_additive]
  ring

section FiniteDiagonal

variable {ι : Type*} [Fintype ι]

/-- A finite diagonal quasilinear form. -/
def diagonalFrobenius (a : ι → R) (e : ℕ) (x : ι → R) : R :=
  ∑ i, a i * frobeniusForm p e (x i)

/-- Polarization on a finite free coordinate family. -/
def vectorPolar (q : (ι → R) → R) (x y : ι → R) : R :=
  q (x + y) - q x - q y

/-- Every finite diagonal Frobenius form has zero polar map. -/
theorem diagonal_frobenius_polar_zero
    (a : ι → R) (e : ℕ) (x y : ι → R) :
    vectorPolar (diagonalFrobenius p a e) x y = 0 := by
  unfold vectorPolar diagonalFrobenius
  simp_rw [Pi.add_apply, frobenius_additive, mul_add]
  rw [Finset.sum_add_distrib]
  ring

end FiniteDiagonal

end PCRLean.Algebra.QuasilinearPolar
