import Mathlib
import PCRLean.CoordinateRootPacket

/-!
# Terminal overlap compatibility for coordinate Frobenius packets

On every standard chart the controlled coordinate root packet is the unit
ideal. Therefore any two chart packets agree at the ideal level. Scheme-level
localization and strict-transform overlap maps remain a later globalization
obligation.
-/

namespace PCRLean
namespace CoordinateTerminalOverlap

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [DecidableEq ι]

/-- Any two standard-chart controlled root ideals are equal. -/
theorem transformedRootIdeal_eq
    (i j : ι) (q : Nat) :
    CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) i q =
      CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) j q :=
  CoordinateRootPacket.transformedRootIdeal_eq
    (R := R) (α := α) i j q

/-- Every chart packet is terminal. -/
theorem terminal_on_every_chart (q : Nat) :
    ∀ i : ι,
      CoordinateRootPacket.transformedRootIdeal
        (R := R) (α := α) i q = ⊤ := by
  intro i
  exact CoordinateRootPacket.transformedRootIdeal_eq_top
    (R := R) (α := α) i q

end

end CoordinateTerminalOverlap
end PCRLean
