import Mathlib
import PCRLean.MarkedIdeal
import PCRLean.CentrePermissibility

namespace PCRLean
namespace OddCuspAffine

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Source coordinate `s`. -/
def sVar : MvPolynomial (Fin 2) R := MvPolynomial.X 0

/-- Source coordinate `y`. -/
def yVar : MvPolynomial (Fin 2) R := MvPolynomial.X 1

/-- The affine odd cusp equation `y^2+s^(2N+1)`. -/
def cusp (N : Nat) : MvPolynomial (Fin 2) R :=
  yVar ^ 2 + sVar ^ (2 * N + 1)

/-- The actual coordinate centre `(s,y)`. -/
def centre : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {sVar, yVar}

/-- The `s`-pivot affine chart homomorphism: `s ↦ s`, `y ↦ sY`. -/
def sPivot : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 0 * MvPolynomial.X 1

/-- The `y`-pivot sibling chart homomorphism: `s ↦ yS`, `y ↦ y`. -/
def yPivot : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 0

@[simp] theorem sPivot_s : sPivot (R := R) (sVar (R := R)) = MvPolynomial.X 0 := by
  simp [sPivot, sVar]

@[simp] theorem sPivot_y :
    sPivot (R := R) (yVar (R := R)) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [sPivot, yVar]

@[simp] theorem yPivot_s :
    yPivot (R := R) (sVar (R := R)) = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  simp [yPivot, sVar]

@[simp] theorem yPivot_y : yPivot (R := R) (yVar (R := R)) = MvPolynomial.X 0 := by
  simp [yPivot, yVar]

/-- Exact controlled-transform identity in the active chart. -/
theorem sPivot_cusp (N : Nat) :
    sPivot (R := R) (cusp (R := R) (N + 1)) =
      (MvPolynomial.X 0) ^ 2 *
        ((MvPolynomial.X 1) ^ 2 + (MvPolynomial.X 0) ^ (2 * N + 1)) := by
  simp [cusp, sPivot, sVar, yVar]
  have hexp : 2 * (N + 1) + 1 = 2 + (2 * N + 1) := by omega
  rw [hexp, pow_add]
  ring

/-- Exact controlled-transform identity in the sibling chart. -/
theorem yPivot_cusp (N : Nat) :
    yPivot (R := R) (cusp (R := R) (N + 1)) =
      (MvPolynomial.X 0) ^ 2 *
        (1 + (MvPolynomial.X 0) ^ (2 * N + 1) *
          (MvPolynomial.X 1) ^ (2 * (N + 1) + 1)) := by
  simp [cusp, yPivot, sVar, yVar]
  have hexp : 2 * (N + 1) + 1 = 2 + (2 * N + 1) := by omega
  rw [hexp, pow_add, mul_pow]
  ring

/-- Both coordinate generators lie in the actual centre. -/
theorem s_mem_centre : sVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp)

theorem y_mem_centre : yVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp)

/-- Every positive-depth odd cusp equation lies in the square of `(s,y)`. -/
theorem cusp_mem_centre_sq (N : Nat) :
    cusp (R := R) (N + 1) ∈ centre (R := R) ^ 2 := by
  have hy2 : yVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq y_mem_centre
  have hs2 : sVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq s_mem_centre
  have hspow : sVar (R := R) ^ (2 * (N + 1) + 1) ∈ centre (R := R) ^ 2 := by
    have hexp : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
    rw [hexp, pow_add]
    exact (centre (R := R) ^ 2).mul_mem_left _ hs2
  exact (centre (R := R) ^ 2).add_mem hy2 hspow

/-- The principal mark-two odd-cusp packet is permissible. -/
theorem marked_cusp_permissible (N : Nat) :
    MarkedIdeal.Permissible
      (R := MvPolynomial (Fin 2) R)
      ⟨Ideal.span {cusp (R := R) (N + 1)}, 2, by omega⟩
      (centre (R := R)) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := MvPolynomial (Fin 2) R) (by omega) (cusp_mem_centre_sq N)

end

end OddCuspAffine
end PCRLean
