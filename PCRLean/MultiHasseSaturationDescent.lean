import Mathlib
import PCRLean.IteratedHasseProduct
import PCRLean.DifferentialIdealSaturation
import PCRLean.DifferentialIdealIteration
import PCRLean.HasseSaturationDescent

/-!
# Canonical saturation for finite products of Frobenius--Hasse frames

`IteratedHasseProduct` proves that the recursively assembled finite primitive
packet on an arbitrary finite product frame generates every matrix unit.  This
file turns that operator-generation theorem into a canonical actual-ideal
construction.

Given a unit-normalized finite free algebra frame, we take the least ideal
containing a seed ideal and stable under the transported finite product packet.
The resulting ideal is exactly extended from its contraction to the base ring.
On Noetherian rings it is reached by finitely many explicit closure steps, and
both the saturation and the descended core are finitely generated.

The remaining geometric bridge is to identify the transported packet with the
intrinsic multivariable Hasse--Cartier operators on smooth Frobenius charts and
to prove that a proper descended core defines a regular permissible centre.
-/

namespace PCRLean
namespace MultiHasseSaturationDescent

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- The transported finite-product primitive operator, viewed as an additive
monoid homomorphism for ideal saturation. -/
def transportedPacketAddHom
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (s : IteratedHasseProduct.MultiPacketIndex spec) : A →+ A where
  toFun := IteratedHasseProduct.pulledBackMultiPrimitivePacket
    (R := R) (A := A) spec F s
  map_zero' := by simp
  map_add' := by
    intro x y
    simp

@[simp] theorem transportedPacketAddHom_apply
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (s : IteratedHasseProduct.MultiPacketIndex spec) (x : A) :
    transportedPacketAddHom spec F s x =
      IteratedHasseProduct.pulledBackMultiPrimitivePacket
        (R := R) (A := A) spec F s x := rfl

/-- The least actual ideal containing `I` and stable under the entire finite
product packet. -/
def saturation
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) : Ideal A :=
  DifferentialIdealSaturation.saturation
    (transportedPacketAddHom spec F) I

/-- The descended base ideal associated with the canonical packet saturation. -/
def core
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) : Ideal R :=
  (saturation spec F I).comap (algebraMap R A)

/-- The seed ideal lies in its canonical finite-product saturation. -/
theorem le_saturation
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    I ≤ saturation spec F I := by
  exact DifferentialIdealSaturation.le_saturation
    (transportedPacketAddHom spec F) I

/-- The canonical saturation is stable under every transported primitive
operator. -/
theorem saturation_stable
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A)
    (s : IteratedHasseProduct.MultiPacketIndex spec) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R)
        (saturation spec F I))
      (IteratedHasseProduct.pulledBackMultiPrimitivePacket
        (R := R) (A := A) spec F s) := by
  intro x hx
  change x ∈ saturation spec F I at hx
  have hs := DifferentialIdealSaturation.saturation_stable
    (transportedPacketAddHom spec F) I s x hx
  simpa using hs

/-- The full finite-product saturation is exactly the extension of its
contraction to the base ring. -/
theorem saturation_eq_map_core
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    saturation spec F I =
      (core spec F I).map (algebraMap R A) := by
  simpa [core] using
    (IteratedHasseProduct.ideal_eq_map_comap_of_multiPrimitive_stable
      (R := R) (A := A) spec F (saturation spec F I)
      (saturation_stable spec F I))

/-- A proper saturation has a proper descended core. -/
theorem core_ne_top_of_saturation_ne_top
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) (hproper : saturation spec F I ≠ ⊤) :
    core spec F I ≠ ⊤ := by
  intro hcore
  apply hproper
  calc
    saturation spec F I =
        (core spec F I).map (algebraMap R A) :=
      saturation_eq_map_core spec F I
    _ = Ideal.map (algebraMap R A) (⊤ : Ideal R) := by rw [hcore]
    _ = ⊤ := HasseSaturationDescent.map_top_algebraMap
      (R := R) (A := A)

/-- Unit saturation is detected exactly after contraction to the base. -/
theorem core_eq_top_iff
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    core spec F I = ⊤ ↔ saturation spec F I = ⊤ := by
  constructor
  · intro hcore
    calc
      saturation spec F I =
          (core spec F I).map (algebraMap R A) :=
        saturation_eq_map_core spec F I
      _ = Ideal.map (algebraMap R A) (⊤ : Ideal R) := by rw [hcore]
      _ = ⊤ := HasseSaturationDescent.map_top_algebraMap
        (R := R) (A := A)
  · intro hsat
    simp [core, hsat]

/-- Canonical product-packet dichotomy: the packet generates the unit ideal,
or it yields a proper actual ideal on the Frobenius base. -/
theorem saturation_dichotomy
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    saturation spec F I = ⊤ ∨
      ∃ C : Ideal R,
        C ≠ ⊤ ∧
        saturation spec F I = C.map (algebraMap R A) := by
  by_cases htop : saturation spec F I = ⊤
  · exact Or.inl htop
  · exact Or.inr ⟨core spec F I,
      core_ne_top_of_saturation_ne_top spec F I htop,
      saturation_eq_map_core spec F I⟩

/-- Canonical finite-product saturation is idempotent. -/
theorem saturation_idempotent
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    saturation spec F (saturation spec F I) = saturation spec F I := by
  exact DifferentialIdealSaturation.saturation_idempotent
    (transportedPacketAddHom spec F) I

section NoetherianAlgebra

variable [IsNoetherianRing A]

/-- The canonical finite-product saturation is finitely generated. -/
theorem saturation_fg
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    (saturation spec F I).FG := by
  exact DifferentialIdealSaturation.saturation_fg
    (transportedPacketAddHom spec F) I

/-- The canonical saturation is reached after finitely many explicit ideal
closure steps. -/
theorem reaches_saturation
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    ∃ J,
      ResolutionCompiler.Reaches
        (DifferentialIdealIteration.Step
          (transportedPacketAddHom spec F)) I J ∧
      J = saturation spec F I := by
  exact DifferentialIdealIteration.reaches_saturation
    (transportedPacketAddHom spec F) I

/-- There is no infinite execution of strict finite-product packet closure
steps on a Noetherian algebra. -/
theorem no_infinite_closure_execution
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec)) :
    ¬ ∃ f : Nat → Ideal A,
      ∀ n,
        DifferentialIdealIteration.Step
          (transportedPacketAddHom spec F) (f n) (f (n + 1)) := by
  exact DifferentialIdealIteration.no_infinite_closure_execution
    (transportedPacketAddHom spec F)

end NoetherianAlgebra

section NoetherianBase

variable [IsNoetherianRing R]

/-- The descended multivariable core is finitely generated. -/
theorem core_fg
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    (core spec F I).FG :=
  IsNoetherian.noetherian _

/-- A finite actual generator set exists for the descended multivariable core. -/
theorem exists_finite_core_generators
    (spec : List (Nat × R))
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec))
    (I : Ideal A) :
    ∃ s : Finset R,
      core spec F I = Ideal.span (s : Set R) := by
  rcases core_fg spec F I with ⟨s, hs⟩
  exact ⟨s, hs.symm⟩

end NoetherianBase

end

end MultiHasseSaturationDescent
end PCRLean
