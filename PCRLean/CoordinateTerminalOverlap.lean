import Mathlib
import PCRLean.CoordinateCentrePrincipalization

/-!
# Terminal overlap compatibility for coordinate Frobenius packets

On every standard chart the controlled coordinate Frobenius packet is the unit
ideal. Therefore any two chart packets agree after restriction to an overlap.
The scheme-level localization map is not needed for this terminal ideal-level
identity.
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
    CoordinateCentrePrincipalization.transformedRootIdeal
        (R := R) (α := α) i q =
      CoordinateCentrePrincipalization.transformedRootIdeal
        (R := R) (α := α) j q := by
  rw [CoordinateCentrePrincipalization.transformedRootIdeal_eq_top,
    CoordinateCentrePrincipalization.transformedRootIdeal_eq_top]

/-- Every chart packet is terminal. -/
theorem terminal_on_every_chart (q : Nat) :
    ∀ i : ι,
      CoordinateCentrePrincipalization.transformedRootIdeal
        (R := R) (α := α) i q = ⊤ := by
  intro i
  exact CoordinateCentrePrincipalization.transformedRootIdeal_eq_top
    (R := R) (α := α) i q

end

end CoordinateTerminalOverlap
end PCRLean
