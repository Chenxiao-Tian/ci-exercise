import Mathlib
import PCRLean.ProductMatrixUnitGeneration
import PCRLean.CoordinatePacketDescent

/-!
# Iterated finite Frobenius--Hasse products

The binary product theorem can be iterated over an arbitrary finite list of
one-variable monogenic Frobenius frames. A frame specification is a list of
pairs `(q,t)`, representing the basis `1,x,...,x^(q-1)` with relation
`x^q = t`. Its coordinate index is the corresponding nested finite product.

For every finite specification, the recursively assembled packet of slice-wise
multiplication and Hasse operators generates every matrix unit. Consequently,
stability under this explicit finite packet gives full endomorphism invariance,
and after transport through a unit-normalized finite free algebra frame it gives
exact ideal descent to the base ring.

This is the finite-dimensional algebraic tensorization needed for arbitrarily
many smooth Frobenius coordinates. The remaining geometric theorem is the
identification of these transported coordinate operators with the intrinsic
Hasse--Cartier operators on actual smooth or etale Frobenius charts.
-/

namespace PCRLean
namespace IteratedHasseProduct

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- Nested product index of a finite list of monogenic frame specifications. -/
def MultiIndex : List (Nat × R) → Type
  | [] => PUnit
  | s :: rest => Fin s.1 × MultiIndex rest

/-- Index type of the recursively assembled finite primitive packet. -/
def MultiPacketIndex : List (Nat × R) → Type
  | [] => Empty
  | s :: rest => (Fin s.1 ⊕ Fin s.1) ⊕ MultiPacketIndex rest

abbrev MultiCoordinates (spec : List (Nat × R)) := MultiIndex spec → R

instance multiIndexFintype (spec : List (Nat × R)) :
    Fintype (MultiIndex spec) := by
  induction spec with
  | nil =>
      simpa [MultiIndex] using (inferInstance : Fintype PUnit)
  | cons s rest ih =>
      letI : Fintype (MultiIndex rest) := ih
      simpa [MultiIndex] using
        (inferInstance : Fintype (Fin s.1 × MultiIndex rest))

instance multiIndexDecidableEq (spec : List (Nat × R)) :
    DecidableEq (MultiIndex spec) := by
  induction spec with
  | nil =>
      simpa [MultiIndex] using (inferInstance : DecidableEq PUnit)
  | cons s rest ih =>
      letI : DecidableEq (MultiIndex rest) := ih
      simpa [MultiIndex] using
        (inferInstance : DecidableEq (Fin s.1 × MultiIndex rest))

/-- Recursive finite multiplication/Hasse packet on the nested product frame. -/
def multiPrimitivePacket :
    (spec : List (Nat × R)) →
      MultiPacketIndex spec → Module.End R (MultiCoordinates spec)
  | [], h => nomatch h
  | s :: rest, k =>
      ProductMatrixUnitGeneration.productPacket
        (FiniteHasseModel.primitivePacket (R := R) s.1 s.2)
        (multiPrimitivePacket rest) k

/-- On the empty product, the unique matrix unit is the identity. -/
theorem punit_matrixUnit :
    MatrixStableSubmodule.matrixUnit (R := R) PUnit.unit PUnit.unit =
      (LinearMap.id : Module.End R (PUnit → R)) := by
  apply LinearMap.ext
  intro z
  funext p
  cases p
  simp [MatrixStableSubmodule.matrixUnit_apply]

/-- The explicit finite multiplication/Hasse packet generates every matrix unit
for an arbitrary finite product specification. -/
theorem multiPrimitivePacket_generatesMatrixUnits
    (spec : List (Nat × R)) :
    EndomorphismGeneration.GeneratesMatrixUnits
      (multiPrimitivePacket (R := R) spec) := by
  induction spec with
  | nil =>
      intro i j
      cases i
      cases j
      rw [punit_matrixUnit (R := R)]
      exact EndomorphismGeneration.Generated.identity
  | cons s rest ih =>
      change EndomorphismGeneration.GeneratesMatrixUnits
        (ProductMatrixUnitGeneration.productPacket
          (FiniteHasseModel.primitivePacket (R := R) s.1 s.2)
          (multiPrimitivePacket (R := R) rest))
      exact ProductMatrixUnitGeneration.productPacket_generatesMatrixUnits
        (FiniteHasseModel.primitivePacket (R := R) s.1 s.2)
        (multiPrimitivePacket (R := R) rest)
        (FiniteHasseModel.primitivePacket_generatesMatrixUnits
          (R := R) s.1 s.2)
        ih

/-- Stability under the recursively assembled finite primitive packet forces
invariance under every endomorphism of the full finite product frame. -/
theorem fullyInvariant_of_multiPrimitive_stable
    (spec : List (Nat × R))
    (N : Submodule R (MultiCoordinates spec))
    (hstable : ∀ s,
      EndomorphismGeneration.StableUnder N
        (multiPrimitivePacket (R := R) spec s)) :
    MatrixStableSubmodule.FullyInvariant N := by
  exact EndomorphismGeneration.fullyInvariant_of_generatesMatrixUnits
    (multiPrimitivePacket (R := R) spec) N
    (multiPrimitivePacket_generatesMatrixUnits (R := R) spec) hstable

section IdealDescent

variable {A : Type v} [CommRing A] [Algebra R A]

/-- Pull the arbitrary finite-product primitive packet back through an actual
unit-normalized finite free algebra frame. -/
def pulledBackMultiPrimitivePacket
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := MultiIndex spec)) :
    MultiPacketIndex spec → Module.End R A :=
  CoordinatePacketDescent.pullbackPacket F.coord
    (multiPrimitivePacket (R := R) spec)

/-- Arbitrary finite-product Frobenius--Hasse ideal descent. -/
theorem ideal_eq_map_comap_of_multiPrimitive_stable
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := MultiIndex spec))
    (I : Ideal A)
    (hstable : ∀ s,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (pulledBackMultiPrimitivePacket
          (R := R) (A := A) spec F s)) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  exact CoordinatePacketDescent.ideal_eq_map_comap_of_pullbackPacket_stable
    F
    (multiPrimitivePacket (R := R) spec)
    (multiPrimitivePacket_generatesMatrixUnits (R := R) spec)
    I hstable

end IdealDescent

end

end IteratedHasseProduct
end PCRLean
