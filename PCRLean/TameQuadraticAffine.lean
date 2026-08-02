import Mathlib
import PCRLean.MarkedIdeal
import PCRLean.CentrePermissibility

namespace PCRLean
namespace TameQuadraticAffine

universe u

variable {R : Type u} [CommRing R]

abbrev P := MvPolynomial (Fin 2) R

def tVar : P := MvPolynomial.X 0

def zVar : P := MvPolynomial.X 1

/-- The tame ramified quadratic branch equation `z^2-u t^N`. -/
def equation (u : R) (N : Nat) : P :=
  zVar ^ 2 - MvPolynomial.C u * tVar ^ N

/-- The collision-cylinder centre `(t,z)`. -/
def centre : Ideal P := Ideal.span {tVar, zVar}

/-- Active `t`-pivot map: `t ↦ t`, `z ↦ tZ`. -/
def tPivot : P →+* P :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 0 * MvPolynomial.X 1

/-- Sibling `z`-pivot map: `t ↦ zT`, `z ↦ z`. -/
def zPivot : P →+* P :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    if i = 0 then MvPolynomial.X 0 * MvPolynomial.X 1 else MvPolynomial.X 0

/-- Exact active-chart controlled transform `N+2 -> N`. -/
theorem tPivot_equation (u : R) (N : Nat) :
    tPivot (R := R) (equation u (N + 2)) =
      (MvPolynomial.X 0) ^ 2 *
        ((MvPolynomial.X 1) ^ 2 - MvPolynomial.C u * (MvPolynomial.X 0) ^ N) := by
  simp [tPivot, equation, tVar, zVar]
  have hexp : N + 2 = 2 + N := by omega
  rw [hexp, pow_add]
  ring

/-- Exact sibling-chart controlled transform; the controlled factor has unit
constant term. -/
theorem zPivot_equation (u : R) (N : Nat) :
    zPivot (R := R) (equation u (N + 2)) =
      (MvPolynomial.X 0) ^ 2 *
        (1 - MvPolynomial.C u * (MvPolynomial.X 0) ^ N *
          (MvPolynomial.X 1) ^ (N + 2)) := by
  simp [zPivot, equation, tVar, zVar]
  have hexp : N + 2 = 2 + N := by omega
  rw [hexp, pow_add, mul_pow]
  ring

theorem t_mem_centre : tVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp [tVar])

theorem z_mem_centre : zVar (R := R) ∈ centre (R := R) := by
  exact Ideal.subset_span (by simp [zVar])

/-- Every positive collision-depth branch equation is mark-two permissible for
`(t,z)`. -/
theorem equation_mem_centre_sq (u : R) (N : Nat) :
    equation (R := R) u (N + 2) ∈ centre (R := R) ^ 2 := by
  have hz2 : zVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq z_mem_centre
  have ht2 : tVar (R := R) ^ 2 ∈ centre (R := R) ^ 2 :=
    CentrePermissibility.square_mem_center_sq t_mem_centre
  have htpow : tVar (R := R) ^ (N + 2) ∈ centre (R := R) ^ 2 := by
    have hexp : N + 2 = N + 2 := rfl
    rw [hexp, pow_add]
    exact (centre (R := R) ^ 2).mul_mem_left _ ht2
  have hcoeff : MvPolynomial.C u * tVar (R := R) ^ (N + 2) ∈ centre (R := R) ^ 2 :=
    (centre (R := R) ^ 2).mul_mem_left _ htpow
  exact (centre (R := R) ^ 2).sub_mem hz2 hcoeff

/-- The corresponding principal marked ideal is permissible. -/
theorem marked_equation_permissible (u : R) (N : Nat) :
    MarkedIdeal.Permissible
      (R := P)
      ⟨Ideal.span {equation (R := R) u (N + 2)}, 2, by omega⟩
      (centre (R := R)) := by
  exact MarkedIdeal.permissible_span_singleton (R := P) (by omega)
    (equation_mem_centre_sq u N)

end TameQuadraticAffine
end PCRLean
