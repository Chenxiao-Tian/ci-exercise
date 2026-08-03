import Mathlib
import PCRLean.MarkedIdeal

/-!
# Experimental hybrid defect--root centre for `y^p - x^(p+1)`

The basic positive-characteristic cusp shows that the actual centre mechanism
cannot be a disjoint choice between an ordinary derivative defect and a pure
Frobenius root. In characteristic `p`, the `y^p` term is invisible to the
ordinary `y` derivative, while the `x^(p+1)` term exposes the `x` direction.
The marked equation is permissible for the hybrid centre `(x,y)`.

Blowing up this hybrid centre gives two explicit chart identities. In the
`x`-pivot chart the controlled transform is `T^p-x`, with unit derivative in
the `x` direction. In the sibling `y`-pivot chart the controlled factor is
`1-y*S^(p+1)`, whose restriction to the exceptional divisor is `1`. Thus the
toy family supplies a complete finite all-chart exit macro.

This file does not prove a universal packet construction or a hereditary
transform theorem beyond this exact chamber.
-/

namespace PCRLean
namespace Experimental
namespace HybridDefectRootCusp

noncomputable section

section RingIdentities

variable {R : Type*} [CommRing R]

/-- Exact `x`-pivot chart identity after substituting `y = x*T` and factoring
the exceptional multiplicity `x^n`. -/
theorem xPivot_identity (x T : R) (n : Nat) :
    (x * T) ^ n - x ^ (n + 1) =
      x ^ n * (T ^ n - x) := by
  rw [mul_pow, pow_succ]
  ring

/-- Exact sibling `y`-pivot chart identity after substituting `x = y*S` and
factoring the exceptional multiplicity `y^n`. -/
theorem yPivot_identity (y S : R) (n : Nat) :
    y ^ n - (y * S) ^ (n + 1) =
      y ^ n * (1 - y * S ^ (n + 1)) := by
  rw [mul_pow, pow_succ]
  ring

/-- The sibling controlled factor has no point on the exceptional divisor:
setting the exceptional coordinate to zero leaves the unit `1`. -/
theorem yPivot_factor_at_exceptional (S : R) (n : Nat) :
    1 - 0 * S ^ (n + 1) = (1 : R) := by
  simp

end RingIdentities

universe u

variable {K : Type u} [Field K]
variable (p : Nat) [Fact p.Prime] [CharP K p]

abbrev P := MvPolynomial Bool K

/-- The ordinary defect coordinate. -/
def x : P (K := K) := MvPolynomial.X false

/-- The Frobenius-root coordinate. -/
def y : P (K := K) := MvPolynomial.X true

/-- The basic cusp equation. -/
def cusp : P (K := K) :=
  (y (K := K)) ^ p - (x (K := K)) ^ (p + 1)

/-- The hybrid actual centre containing both the visible defect and the
Frobenius-root direction. -/
def hybridIdeal : Ideal (P (K := K)) :=
  Ideal.span {x (K := K), y (K := K)}

/-- The defect coordinate belongs to the hybrid centre. -/
theorem x_mem_hybridIdeal :
    x (K := K) ∈ hybridIdeal (K := K) := by
  apply Ideal.subset_span
  simp

/-- The root coordinate belongs to the hybrid centre. -/
theorem y_mem_hybridIdeal :
    y (K := K) ∈ hybridIdeal (K := K) := by
  apply Ideal.subset_span
  simp

/-- The Frobenius term lies in the marked centre power. -/
theorem y_pow_mem_hybridIdeal_pow :
    (y (K := K)) ^ p ∈ (hybridIdeal (K := K)) ^ p :=
  Ideal.pow_mem_pow (y_mem_hybridIdeal (K := K)) p

/-- The higher ordinary defect term also lies in the same marked power. -/
theorem x_pow_succ_mem_hybridIdeal_pow :
    (x (K := K)) ^ (p + 1) ∈ (hybridIdeal (K := K)) ^ p := by
  rw [pow_succ]
  exact ((hybridIdeal (K := K)) ^ p).mul_mem_right
    (x (K := K))
    (Ideal.pow_mem_pow (x_mem_hybridIdeal (K := K)) p)

/-- Exact marked-power containment for the hybrid centre. -/
theorem cusp_mem_hybridIdeal_pow :
    cusp (K := K) p ∈ (hybridIdeal (K := K)) ^ p := by
  rw [cusp]
  exact ((hybridIdeal (K := K)) ^ p).sub_mem
    (y_pow_mem_hybridIdeal_pow (K := K) p)
    (x_pow_succ_mem_hybridIdeal_pow (K := K) p)

/-- The cusp packet of mark `p` is permissible for the actual hybrid centre. -/
theorem markedCusp_permissible :
    MarkedIdeal.Permissible
      (R := P (K := K))
      ⟨Ideal.span {cusp (K := K) p}, p, Fact.out.pos⟩
      (hybridIdeal (K := K)) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := P (K := K)) Fact.out.pos
    (cusp_mem_hybridIdeal_pow (K := K) p)

/-- The ordinary derivative in the Frobenius-root direction vanishes. -/
theorem pderiv_y_cusp :
    MvPolynomial.pderiv true (cusp (K := K) p) = 0 := by
  have hp : (p : P (K := K)) = 0 :=
    CharP.cast_eq_zero (P (K := K)) p
  simp [cusp, x, y, MvPolynomial.pderiv_pow, hp]

/-- The ordinary derivative in the defect direction is the negative `p`th
power of `x`. -/
theorem pderiv_x_cusp :
    MvPolynomial.pderiv false (cusp (K := K) p) =
      -((x (K := K)) ^ p) := by
  have hp : (p : P (K := K)) = 0 :=
    CharP.cast_eq_zero (P (K := K)) p
  have hp1 : ((p + 1 : Nat) : P (K := K)) = 1 := by
    rw [Nat.cast_add, hp]
    simp
  simp [cusp, x, y, MvPolynomial.pderiv_pow, hp, hp1]

/-- Controlled transform on the active `x`-pivot chart. -/
def activeTransform : P (K := K) :=
  (y (K := K)) ^ p - x (K := K)

/-- The active transform is smooth in the defect coordinate: its partial
derivative is the unit `-1`. -/
theorem pderiv_x_activeTransform :
    MvPolynomial.pderiv false (activeTransform (K := K) p) = -1 := by
  simp [activeTransform, x, y, MvPolynomial.pderiv_pow]

/-- The remaining Frobenius direction of the active transform is still
ordinary-derivative invisible. -/
theorem pderiv_y_activeTransform :
    MvPolynomial.pderiv true (activeTransform (K := K) p) = 0 := by
  have hp : (p : P (K := K)) = 0 :=
    CharP.cast_eq_zero (P (K := K)) p
  simp [activeTransform, x, y, MvPolynomial.pderiv_pow, hp]

end

end HybridDefectRootCusp
end Experimental
end PCRLean
