import Mathlib
import PCRLean.EndomorphismGeneration
import PCRLean.IdealEndomorphismDescent

/-!
# Descent from a coordinate operator packet

A finite free algebra equipped with a unit-normalized coordinate frame inherits
endomorphisms from any packet on its coordinate module by conjugation. If the
coordinate packet generates the matrix units, stability of an ideal under the
transported packet forces the ideal to descend from the base ring.

This file is the formal transport bridge used to apply the finite
Frobenius--Hasse coordinate model to actual local algebras. The remaining
chart-specific task is to identify the transported multiplication and Hasse
operators with the intrinsic operators on a polynomial, monogenic or etale
Frobenius chart.
-/

namespace PCRLean
namespace CoordinatePacketDescent

noncomputable section

universe u v w x

variable {R : Type u} {A : Type v} {ι : Type w} {κ : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]

abbrev Coordinates := ι → R

/-- Transport a coordinate endomorphism back to the actual finite free
module. -/
def pullbackOperator
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (T : Module.End R (Coordinates (R := R) (ι := ι))) :
    Module.End R A :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

@[simp] theorem pullbackOperator_apply
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (T : Module.End R (Coordinates (R := R) (ι := ι)))
    (x : A) :
    e (pullbackOperator e T x) = T (e x) := by
  simp [pullbackOperator]

/-- Conjugating a pulled-back coordinate operator forward recovers the original
operator exactly. -/
theorem conjugate_pullbackOperator
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (T : Module.End R (Coordinates (R := R) (ι := ι))) :
    EndomorphismGeneration.conjugateToCoordinates e
        (pullbackOperator e T) = T := by
  ext y
  simp [EndomorphismGeneration.conjugateToCoordinates, pullbackOperator]

/-- Pull back every operator in a coordinate packet. -/
def pullbackPacket
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι))) :
    κ → Module.End R A :=
  fun k => pullbackOperator e (ops k)

/-- The conjugated pullback packet is the original coordinate packet. -/
theorem conjugated_pullbackPacket
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (k : κ) :
    EndomorphismGeneration.conjugateToCoordinates e
      (pullbackPacket e ops k) = ops k := by
  exact conjugate_pullbackOperator e (ops k)

/-- Matrix-unit generation is preserved when a coordinate packet is pulled
back and then conjugated forward by the same frame. -/
theorem conjugated_pullback_generatesMatrixUnits
    (e : A ≃ₗ[R] Coordinates (R := R) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops) :
    EndomorphismGeneration.GeneratesMatrixUnits
      (fun k => EndomorphismGeneration.conjugateToCoordinates e
        (pullbackPacket e ops k)) := by
  have heq :
      (fun k => EndomorphismGeneration.conjugateToCoordinates e
        (pullbackPacket e ops k)) = ops := by
    funext k
    exact conjugated_pullbackPacket e ops k
  rw [heq]
  exact hgen

/-- Main transport theorem: an ideal stable under the pullback of a
matrix-unit-generating coordinate packet is extended from its contraction to
the base ring. -/
theorem ideal_eq_map_comap_of_pullbackPacket_stable
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R (Coordinates (R := R) (ι := ι)))
    (hgen : EndomorphismGeneration.GeneratesMatrixUnits ops)
    (I : Ideal A)
    (hstable : ∀ k,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (pullbackPacket F.coord ops k)) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply EndomorphismGeneration.ideal_eq_map_comap_of_generated_matrixUnits
    F (pullbackPacket F.coord ops) I
  · exact conjugated_pullback_generatesMatrixUnits F.coord ops hgen
  · exact hstable

end

end CoordinatePacketDescent
end PCRLean
