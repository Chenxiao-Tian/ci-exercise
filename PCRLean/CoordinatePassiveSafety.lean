import Mathlib
import PCRLean.CoordinateBlowupChart

/-!
# Passive-coordinate invariance on standard blowup charts

Every standard chart of the coordinate-centre blowup fixes each passive
coordinate.  Consequently it fixes every power of every passive coordinate.
This is the generatorwise ring-map component of hereditary passive safety in
the split coordinate chamber.  Full normal-flatness is kept as a separate
module-theoretic gate.
-/

namespace PCRLean
namespace CoordinatePassiveSafety

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [DecidableEq ι]

/-- A standard chart fixes each passive coordinate. -/
theorem passiveVar_fixed (k : ι) (a : α) :
    CoordinateBlowupChart.chartMap (R := R) (α := α) k
        (CoordinateBlowupChart.passiveVar (R := R) (ι := ι) a) =
      CoordinateBlowupChart.passiveVar (R := R) (ι := ι) a :=
  CoordinateBlowupChart.chartMap_passiveVar
    (R := R) (α := α) k a

/-- A standard chart fixes every power of a passive coordinate. -/
theorem passiveVar_pow_fixed (k : ι) (a : α) (n : Nat) :
    CoordinateBlowupChart.chartMap (R := R) (α := α) k
        ((CoordinateBlowupChart.passiveVar
          (R := R) (ι := ι) a) ^ n) =
      (CoordinateBlowupChart.passiveVar
        (R := R) (ι := ι) a) ^ n := by
  rw [map_pow, passiveVar_fixed]

/-- Products of two passive coordinate powers are chart-invariant. -/
theorem passiveProduct_fixed
    (k : ι) (a b : α) (m n : Nat) :
    CoordinateBlowupChart.chartMap (R := R) (α := α) k
        ((CoordinateBlowupChart.passiveVar
            (R := R) (ι := ι) a) ^ m *
          (CoordinateBlowupChart.passiveVar
            (R := R) (ι := ι) b) ^ n) =
      (CoordinateBlowupChart.passiveVar
          (R := R) (ι := ι) a) ^ m *
        (CoordinateBlowupChart.passiveVar
          (R := R) (ι := ι) b) ^ n := by
  rw [map_mul, passiveVar_pow_fixed, passiveVar_pow_fixed]

end

end CoordinatePassiveSafety
end PCRLean
