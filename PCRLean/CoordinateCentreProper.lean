import Mathlib
import PCRLean.CoordinateBlowupChart

/-!
# Properness of the coordinate centre

Evaluation of every ambient variable at zero annihilates the coordinate centre
ideal but not the unit.  Hence the coordinate centre is a genuine nonidentity
closed subscheme whenever the coefficient ring is nontrivial.
-/

namespace PCRLean
namespace CoordinateCentreProper

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {α : Type v} {ι : Type w}

abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

/-- Evaluation at the origin of affine coordinate space. -/
def zeroEval : P (K := K) (α := α) (ι := ι) →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun _ => 0)

/-- The coordinate centre is contained in the kernel of evaluation at the
origin. -/
theorem centreIdeal_le_zeroEvalKer :
    CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) ≤
      RingHom.ker (zeroEval (K := K) (α := α) (ι := ι)) := by
  rw [CoordinateBlowupChart.centreIdeal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  simp [zeroEval, CoordinateBlowupChart.centreVar]

/-- The coordinate centre is proper. -/
theorem centreIdeal_ne_top [Nontrivial K] :
    CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι) ≠ ⊤ := by
  intro htop
  have hunit :
      (1 : P (K := K) (α := α) (ι := ι)) ∈
        CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι) := by
    rw [htop]
    trivial
  have hker := centreIdeal_le_zeroEvalKer
    (K := K) (α := α) (ι := ι) hunit
  have hzero := RingHom.mem_ker.mp hker
  simpa [zeroEval] using hzero

end

end CoordinateCentreProper
end PCRLean
