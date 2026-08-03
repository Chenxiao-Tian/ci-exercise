import Mathlib
import PCRLean.MarkedIdeal

namespace PCRLean
namespace CentrePermissibility

variable {R : Type*} [CommRing R]

/-- A square of an element of the centre lies in the square of the centre. -/
theorem square_mem_center_sq {C : Ideal R} {a : R} (ha : a ∈ C) :
    a ^ 2 ∈ C ^ 2 := by
  exact Ideal.pow_mem_pow ha 2

/-- A product of two centre generators lies in the square of the centre. -/
theorem mul_mem_center_sq {C : Ideal R} {a b : R}
    (ha : a ∈ C) (hb : b ∈ C) : a * b ∈ C ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul ha hb

/-- Every binary quadratic expression with coefficients in the ambient ring
is contained in the square of a centre containing both variables. -/
theorem binary_quadratic_mem_center_sq {C : Ideal R} {a b α β γ : R}
    (ha : a ∈ C) (hb : b ∈ C) :
    α * a ^ 2 + β * (a * b) + γ * b ^ 2 ∈ C ^ 2 := by
  have ha2 : a ^ 2 ∈ C ^ 2 := square_mem_center_sq ha
  have hab : a * b ∈ C ^ 2 := mul_mem_center_sq ha hb
  have hb2 : b ^ 2 ∈ C ^ 2 := square_mem_center_sq hb
  exact (C ^ 2).add_mem
    ((C ^ 2).add_mem ((C ^ 2).mul_mem_left α ha2)
      ((C ^ 2).mul_mem_left β hab))
    ((C ^ 2).mul_mem_left γ hb2)

/-- The tame ramified quadratic equation is mark-two permissible for any
centre containing its two quadratic variables. -/
theorem tame_quadratic_permissible {C : Ideal R} {a b t u : R} (N : Nat)
    (ha : a ∈ C) (hb : b ∈ C) :
    a ^ 2 - u * t ^ N * b ^ 2 ∈ C ^ 2 := by
  have h := binary_quadratic_mem_center_sq (C := C)
    (a := a) (b := b) (α := 1) (β := 0) (γ := -(u * t ^ N)) ha hb
  simpa [sub_eq_add_neg] using h

/-- The Artin--Schreier quadratic packet is mark-two permissible for any
centre containing `a` and `b`. -/
theorem artinSchreier_quadratic_permissible {C : Ideal R}
    {a b t u : R} (m r : Nat) (ha : a ∈ C) (hb : b ∈ C) :
    a ^ 2 + t ^ m * (a * b) + u * t ^ r * b ^ 2 ∈ C ^ 2 := by
  simpa [mul_assoc] using
    binary_quadratic_mem_center_sq (C := C)
      (a := a) (b := b) (α := 1) (β := t ^ m) (γ := u * t ^ r) ha hb

/-- The corresponding principal marked ideal is permissible. -/
theorem artinSchreier_marked_packet_permissible {C : Ideal R}
    {a b t u : R} (m r : Nat) (ha : a ∈ C) (hb : b ∈ C) :
    MarkedIdeal.Permissible
      (R := R)
      ⟨Ideal.span {a ^ 2 + t ^ m * (a * b) + u * t ^ r * b ^ 2}, 2, by omega⟩ C := by
  exact MarkedIdeal.permissible_span_singleton (R := R) (by omega)
    (artinSchreier_quadratic_permissible m r ha hb)

/-- More generally, a sum of two marked-square terms remains permissible. -/
theorem sum_of_squares_mem {C : Ideal R} {a b : R}
    (ha : a ∈ C) (hb : b ∈ C) : a ^ 2 + b ^ 2 ∈ C ^ 2 := by
  exact (C ^ 2).add_mem (square_mem_center_sq ha) (square_mem_center_sq hb)

end CentrePermissibility
end PCRLean
