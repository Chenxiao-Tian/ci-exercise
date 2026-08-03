import Mathlib
import PCRLean.CoordinatePacketDescent
import PCRLean.IdealOperatorPacketDescent

/-!
# Ideal descent from a classified operator packet

The recursive multivariable Frobenius packet need not be presented as one
literal sum of a multiplication family and a differential family.  It is
enough to classify each generator separately: after transport to the actual
algebra, the generator is either multiplication by an algebra element, or it
preserves the ideal under study.

If the coordinate packet generates every matrix unit, this pointwise
dichotomy supplies stability under the entire pulled-back packet and hence
exact descent of the ideal from the base ring.
-/

namespace PCRLean
namespace OperatorPacketDichotomyDescent

noncomputable section

universe u v w x

variable {R : Type u} {A : Type v} {ι : Type w} {κ : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R

/-- One transported packet generator is either actual multiplication or is
known directly to preserve the ideal. -/
def MultiplicationOrStable
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (I : Ideal A) (k : κ) : Prop :=
  (∃ a : A,
    CoordinatePacketDescent.pullbackPacket F.coord ops k =
      IdealOperatorPacketDescent.leftMultiplication (R := R) a) ∨
  EndomorphismGeneration.StableUnder
    (IdealEndomorphismDescent.idealSubmodule (R := R) I)
    (CoordinatePacketDescent.pullbackPacket F.coord ops k)

/-- A classified generator preserves the ideal. -/
theorem stable_of_multiplicationOrStable
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (I : Ideal A) (k : κ)
    (h : MultiplicationOrStable F ops I k) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R) I)
      (CoordinatePacketDescent.pullbackPacket F.coord ops k) := by
  rcases h with ⟨a, ha⟩ | hstable
  · rw [ha]
    exact IdealOperatorPacketDescent.leftMultiplication_stable
      (R := R) I a
  · exact hstable

/-- Main classified-packet descent theorem.  The coordinate packet may be
assembled recursively or by a finite atlas; only matrix-unit generation and
the pointwise multiplication-or-stability classification are required. -/
theorem ideal_eq_map_comap_of_classified_packet
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops)
    (I : Ideal A)
    (hclass : ∀ k, MultiplicationOrStable F ops I k) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  exact CoordinatePacketDescent.ideal_eq_map_comap_of_pullbackPacket_stable
    F ops hgen I
    (fun k => stable_of_multiplicationOrStable F ops I k (hclass k))

/-- The same conclusion when the classification is supplied as an explicit
function returning either a multiplication witness or a stability proof. -/
theorem ideal_eq_map_comap_of_generator_dichotomy
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops)
    (I : Ideal A)
    (hclass : ∀ k,
      (∃ a : A,
        CoordinatePacketDescent.pullbackPacket F.coord ops k =
          IdealOperatorPacketDescent.leftMultiplication (R := R) a) ∨
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackPacket F.coord ops k)) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  exact ideal_eq_map_comap_of_classified_packet F ops hgen I hclass

end

end OperatorPacketDichotomyDescent
end PCRLean
