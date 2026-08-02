import Mathlib
import Mathlib.Algebra.CharP.Two

/-!
# Characteristic-two cleaning and Artin-Schreier gauge identities

The identities in this file formalize the exact gauge action used throughout
the characteristic-two branches of the PCR program.  They ensure that a
cleaning translation is represented by an equality rather than by an informal
change of presentation.
-/

namespace PCRLean.Algebra.CharacteristicTwoGauge

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Frobenius additivity for a square in characteristic two. -/
theorem add_square (x g : R) :
    (x + g) ^ 2 = x ^ 2 + g ^ 2 :=
  CharTwo.add_sq x g

/-- A characteristic-two translation is its own inverse. -/
theorem translate_twice (x g : R) :
    (x + g) + g = x := by
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Exact cleaning identity for a purely inseparable quadratic presentation. -/
theorem purelyInseparable_cleaning (y g u : R) :
    (y + g) ^ 2 + u = y ^ 2 + (u + g ^ 2) := by
  rw [CharTwo.add_sq]
  ac_rfl

/-- Exact cleaning identity for an Artin-Schreier quadratic presentation.
The linear coefficient is unchanged, while the tail changes by
`g^2 + a*g`. -/
theorem artinSchreier_cleaning (y g a u : R) :
    (y + g) ^ 2 + a * (y + g) + u =
      y ^ 2 + a * y + (u + g ^ 2 + a * g) := by
  rw [CharTwo.add_sq]
  ring

/-- Two successive cleaners compose by addition. -/
theorem cleaners_compose (y g h : R) :
    (y + g) + h = y + (g + h) := by
  simp [add_assoc]

/-- The Artin-Schreier tail update is compatible with composition of cleaners. -/
theorem tail_update_compose (a u g h : R) :
    (u + g ^ 2 + a * g) + h ^ 2 + a * h =
      u + (g + h) ^ 2 + a * (g + h) := by
  rw [CharTwo.add_sq]
  ring

/-- In the purely inseparable case, adding a square cleaner does not alter the
difference between two cleaned tails modulo the square image. -/
theorem purelyInseparable_tail_difference (u g h : R) :
    (u + g ^ 2) - (u + h ^ 2) = g ^ 2 + h ^ 2 := by
  simp only [CharTwo.sub_eq_add]
  ring

end PCRLean.Algebra.CharacteristicTwoGauge
