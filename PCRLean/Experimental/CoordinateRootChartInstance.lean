import Mathlib
import PCRLean.CoordinateBlowupChart
import PCRLean.CoordinateRootPacket
import PCRLean.Experimental.AbstractRootChartTerminality

/-!
# Coordinate instance of the abstract root-chart interface

The standard coordinate-centre blowup chart is an instance of the abstract
pivot-root chart.  The exceptional element is the pivot coordinate and the
controlled roots are the existing explicit root transforms.  Hence the
abstract terminality theorem reproduces the coordinate all-chart theorem.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateRootChartInstance

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [Fintype ι] [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := R) (α := α) (ι := ι)

/-- Coordinate pivot chart as an abstract root chart. -/
def rootChart (k : ι) :
    AbstractRootChartTerminality.RootChart
      (fun i : ι =>
        CoordinateBlowupChart.centreVar (R := R) (α := α) i)
      k where
  chartMap := CoordinateBlowupChart.chartMap (R := R) (α := α) k
  exceptional := CoordinateBlowupChart.centreVar (R := R) (α := α) k
  controlledRoot := CoordinateRootPacket.explicitRootTransform
    (R := R) (α := α) k
  factorization := by
    intro i
    exact CoordinateRootPacket.centreVar_factorization
      (R := R) (α := α) k i
  pivot_controlledRoot := by
    simp [CoordinateRootPacket.explicitRootTransform]

/-- The abstract transformed root ideal is definitionally the existing
coordinate transformed root ideal. -/
theorem transformedRootIdeal_eq_coordinate
    (k : ι) (q : Nat) :
    (rootChart (R := R) (α := α) k).transformedRootIdeal q =
      CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) k q := by
  rfl

/-- Coordinate all-chart terminality follows from the abstract pivot-root
theorem. -/
theorem transformedRootIdeal_eq_top
    (k : ι) (q : Nat) :
    CoordinateRootPacket.transformedRootIdeal
      (R := R) (α := α) k q = ⊤ := by
  rw [← transformedRootIdeal_eq_coordinate]
  exact (rootChart (R := R) (α := α) k).transformedRootIdeal_eq_top q

/-- Coordinate chart overlap equality follows abstractly because every full
root packet is top. -/
theorem transformedRootIdeal_eq
    (i j : ι) (q : Nat) :
    CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) i q =
      CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) j q := by
  rw [← transformedRootIdeal_eq_coordinate,
    ← transformedRootIdeal_eq_coordinate]
  exact (rootChart (R := R) (α := α) i).transformedRootIdeal_eq
    (rootChart (R := R) (α := α) j) q

end

end CoordinateRootChartInstance
end Experimental
end PCRLean
