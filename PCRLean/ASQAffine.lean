import Mathlib
import PCRLean.MarkedIdeal
import PCRLean.CentrePermissibility

namespace PCRLean
namespace ASQAffine

noncomputable section

universe u

variable {R : Type u} [CommRing R]

def tVar : MvPolynomial (Fin 2) R := MvPolynomial.X 0

def zVar : MvPolynomial (Fin 2) R := MvPolynomial.X 1

/-- Artin--Schreier quadratic branch equation. -/
def equation (u : R) (m r : Nat) : MvPolynomial (Fin 2) R :=
  zVar ^ 2 + tVar ^ m * zVar + MvPolynomial.C u * tVar ^ r

/-- The collision-cylinder centre `(t,z)`. -/
def centre : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {tVar, zVar}

/-- Active `t`-pivot: `t ↦ t`, `z ↦ tZ`. -/
def tPivot : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 0 * MvPolynomial.X 1

/-- Sibling `z`-pivot: `t ↦ zT`, `z ↦ z`. -/
def zPivot : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 0

/-- Exact active-chart recurrence `(m+1,r+2) -> (m,r)`. -/
theorem tPivot_equation (u : R) (m r : Nat) :
    tPivot (R := R) (equation (R := R) u (m + 1) (r + 2)) =
      (MvPolynomial.X 0) ^ 2 *
        ((MvPolynomial.X 1) ^ 2 +
          (MvPolynomial.X 0) ^ m * MvPolynomial.X 1 +
          MvPolynomial.C u * (MvPolynomial.X 0) ^ r) := by
  simp [tPivot, equation, tVar, zVar]
  have hr : r + 2 = 2 + r := by omega
  rw [pow_succ, hr, pow_add]
  ring

/-- Exact sibling-chart transform; the controlled factor begins with `1`. -/
theorem zPivot_equation (u : R) (m r : Nat) :
    zPivot (R := R) (equation (R := R) u (m + 1) (r + 2)) =
      (MvPolynomial.X 0) ^ 2 *
        (1 + (MvPolynomial.X 0) ^ m *
          (MvPolynomial.X 1) ^ (m + 1) +
          MvPolynomial.C u * (MvPolynomial.X 0) ^ r *
            (MvPolynomial.X 1) ^ (r + 2)) := by
  simp [zPivot, equation, tVar, zVar]
  have hr : r + 2 = 2 + r := by omega
  rw [mul_pow, pow_succ, hr, pow_add]
  ring

theorem t_mem_centre : tVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp)

theorem z_mem_centre : zVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp)

/-- The active ASQ equation with at least one `t` in the linear term and at
least two in the tail is mark-two permissible for `(t,z)`. -/
theorem equation_mem_centre_sq (u : R) (m r : Nat) :
    equation (R := R) u (m + 1) (r + 2) ∈ centre (R := R) ^ 2 := by
  have hz2 : zVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq z_mem_centre
  have htz : tVar (R := R) * zVar (R := R) ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.mul_mem_center_sq t_mem_centre z_mem_centre
  have hlinear : tVar (R := R) ^ (m + 1) * zVar (R := R) ∈ centre (R := R) ^ 2 := by
    have hmul := (centre (R := R) ^ 2).mul_mem_left
      (tVar (R := R) ^ m) htz
    simpa [pow_succ, mul_assoc] using hmul
  have ht2 : tVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq t_mem_centre
  have htailPow : tVar (R := R) ^ (r + 2) ∈ centre (R := R) ^ 2 := by
    rw [pow_add]
    exact (centre (R := R) ^ 2).mul_mem_left _ ht2
  have htail : MvPolynomial.C u * tVar (R := R) ^ (r + 2) ∈ centre (R := R) ^ 2 :=
    (centre (R := R) ^ 2).mul_mem_left _ htailPow
  exact (centre (R := R) ^ 2).add_mem
    ((centre (R := R) ^ 2).add_mem hz2 hlinear) htail

/-- The principal mark-two ASQ packet is permissible. -/
theorem marked_equation_permissible (u : R) (m r : Nat) :
    MarkedIdeal.Permissible
      (R := MvPolynomial (Fin 2) R)
      ⟨Ideal.span {equation (R := R) u (m + 1) (r + 2)}, 2, by omega⟩
      (centre (R := R)) := by
  exact MarkedIdeal.permissible_span_singleton
    (R := MvPolynomial (Fin 2) R) (by omega)
    (equation_mem_centre_sq u m r)

end

end ASQAffine
end PCRLean
