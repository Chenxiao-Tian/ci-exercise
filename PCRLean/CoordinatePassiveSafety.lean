import Mathlib
import PCRLean.CoordinateBlowupChart

/-!
# MLEL-002: passive-base invariance on coordinate blowup charts

The standard coordinate blowup chart fixes every passive variable. Therefore it
fixes the entire passive polynomial subring and every ideal extended from that
subring. This is the ring-map component of hereditary passive safety in the
coordinate split chamber.

The Tor/Koszul and associated-graded statements are proved mathematically in
the MLEL-002 strengthening report and are not yet formalized here.
-/

namespace PCRLean
namespace CoordinatePassiveSafety

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [DecidableEq ι]

abbrev PassiveRing := MvPolynomial α R
abbrev P := CoordinateBlowupChart.P (R := R) (α := α) (ι := ι)

/-- Embed the passive polynomial ring into the ambient ring. -/
def passiveEmbed : PassiveRing (R := R) (α := α) →+*
    P (R := R) (α := α) (ι := ι) :=
  MvPolynomial.rename Sum.inl

/-- Every coordinate blowup chart restricts to the identity on the passive
subring. -/
theorem chartMap_comp_passiveEmbed (k : ι) :
    (CoordinateBlowupChart.chartMap (R := R) (α := α) k).comp
        (passiveEmbed (R := R) (α := α) (ι := ι)) =
      passiveEmbed (R := R) (α := α) (ι := ι) := by
  ext a
  simp [passiveEmbed, CoordinateBlowupChart.chartMap]

/-- Pointwise passive-polynomial invariance. -/
theorem chartMap_passivePolynomial (k : ι)
    (f : PassiveRing (R := R) (α := α)) :
    CoordinateBlowupChart.chartMap (R := R) (α := α) k
        (passiveEmbed (R := R) (α := α) (ι := ι) f) =
      passiveEmbed (R := R) (α := α) (ι := ι) f := by
  have h := congrArg
    (fun φ : PassiveRing (R := R) (α := α) →+*
        P (R := R) (α := α) (ι := ι) => φ f)
    (chartMap_comp_passiveEmbed (R := R) (α := α) k)
  simpa using h

/-- Every ideal extended from the passive subring is exactly chart-invariant. -/
theorem map_extendedPassiveIdeal_eq
    (k : ι) (J : Ideal (PassiveRing (R := R) (α := α))) :
    (J.map (passiveEmbed (R := R) (α := α) (ι := ι))).map
        (CoordinateBlowupChart.chartMap (R := R) (α := α) k) =
      J.map (passiveEmbed (R := R) (α := α) (ι := ι)) := by
  rw [Ideal.map_map, chartMap_comp_passiveEmbed]

end

end CoordinatePassiveSafety
end PCRLean
