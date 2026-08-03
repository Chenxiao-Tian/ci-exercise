import Mathlib
import PCRLean.IteratedHasseProduct
import PCRLean.IdealOperatorPacketDescent
import PCRLean.DifferentialIdealSaturation
import PCRLean.DifferentialIdealIteration
import PCRLean.HasseSaturationDescent

/-!
# Hasse-only descent on realized finite product frames

The recursively assembled packet of `IteratedHasseProduct` contains two kinds
of generators: coordinate multiplication operators and Hasse operators.
For an actual ideal, the multiplication generators require no saturation once
they have been identified with multiplication by elements of the algebra.

This file separates the two kinds of packet indices. A realized product frame
supplies an actual multiplication witness for every multiplication index. We
then saturate only under the Hasse indices. The resulting ideal is nevertheless
stable under the full primitive packet, hence descends exactly from the base
ring. On a Noetherian algebra this Hasse-only saturation is reached by finitely
many strict actual-ideal closure steps.

The remaining geometric task is to build these realized product frames from
intrinsic smooth Frobenius coordinates and to prove compatibility on overlaps.
-/

namespace PCRLean
namespace MultiHasseOnlyDescent

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- Indices of multiplication generators in a recursive product packet. -/
def MultiplicationIndex : List (Nat × R) → Type
  | [] => Empty
  | s :: rest => Fin s.1 ⊕ MultiplicationIndex rest

/-- Indices of Hasse generators in a recursive product packet. -/
def HasseIndex : List (Nat × R) → Type
  | [] => Empty
  | s :: rest => Fin s.1 ⊕ HasseIndex rest

/-- Embed a multiplication index into the full primitive packet. -/
def embedMultiplication :
    (spec : List (Nat × R)) →
      MultiplicationIndex spec → IteratedHasseProduct.MultiPacketIndex spec
  | [], h => nomatch h
  | s :: rest, Sum.inl m => Sum.inl (Sum.inl m)
  | s :: rest, Sum.inr m => Sum.inr (embedMultiplication rest m)

/-- Embed a Hasse index into the full primitive packet. -/
def embedHasse :
    (spec : List (Nat × R)) →
      HasseIndex spec → IteratedHasseProduct.MultiPacketIndex spec
  | [], h => nomatch h
  | s :: rest, Sum.inl d => Sum.inl (Sum.inr d)
  | s :: rest, Sum.inr d => Sum.inr (embedHasse rest d)

/-- Classify every primitive packet generator as multiplication or Hasse. -/
def classify :
    (spec : List (Nat × R)) →
      IteratedHasseProduct.MultiPacketIndex spec →
        MultiplicationIndex spec ⊕ HasseIndex spec
  | [], h => nomatch h
  | s :: rest, Sum.inl (Sum.inl m) => Sum.inl (Sum.inl m)
  | s :: rest, Sum.inl (Sum.inr d) => Sum.inr (Sum.inl d)
  | s :: rest, Sum.inr k =>
      match classify rest k with
      | Sum.inl m => Sum.inl (Sum.inr m)
      | Sum.inr d => Sum.inr (Sum.inr d)

/-- Re-embed a classified packet index into the full packet. -/
def embedClassified
    (spec : List (Nat × R)) :
    MultiplicationIndex spec ⊕ HasseIndex spec →
      IteratedHasseProduct.MultiPacketIndex spec
  | Sum.inl m => embedMultiplication spec m
  | Sum.inr d => embedHasse spec d

/-- Classification loses no packet-index information. -/
theorem embed_classify
    (spec : List (Nat × R))
    (k : IteratedHasseProduct.MultiPacketIndex spec) :
    embedClassified spec (classify spec k) = k := by
  induction spec with
  | nil => exact nomatch k
  | cons s rest ih =>
      cases k with
      | inl h =>
          cases h <;> rfl
      | inr k =>
          cases hclass : classify rest k with
          | inl m =>
              have hk := ih k
              rw [hclass] at hk
              have hout :
                  classify (s :: rest) (Sum.inr k) =
                    Sum.inl (Sum.inr m) := by
                simp only [classify, hclass]
                rfl
              rw [hout]
              change Sum.inr (embedMultiplication rest m) = Sum.inr k
              exact congrArg Sum.inr hk
          | inr d =>
              have hk := ih k
              rw [hclass] at hk
              have hout :
                  classify (s :: rest) (Sum.inr k) =
                    Sum.inr (Sum.inr d) := by
                simp only [classify, hclass]
                rfl
              rw [hout]
              change Sum.inr (embedHasse rest d) = Sum.inr k
              exact congrArg Sum.inr hk

/-- A finite-product frame whose multiplication packet has been realized by
actual multiplication in the algebra. -/
structure RealizedFrame (spec : List (Nat × R)) where
  unitFrame : IdealEndomorphismDescent.UnitFrame
    (R := R) (A := A) (ι := IteratedHasseProduct.MultiIndex spec)
  multiplicationRealization :
    ∀ m : MultiplicationIndex spec,
      ∃ a : A,
        IteratedHasseProduct.pulledBackMultiPrimitivePacket
            (R := R) (A := A) spec unitFrame
            (embedMultiplication spec m) =
          IdealOperatorPacketDescent.leftMultiplication (R := R) a

namespace RealizedFrame

variable {spec : List (Nat × R)}
variable (F : RealizedFrame (R := R) (A := A) spec)

/-- One actually transported Hasse generator. -/
def hasseOperator (d : HasseIndex spec) : Module.End R A :=
  IteratedHasseProduct.pulledBackMultiPrimitivePacket
    (R := R) (A := A) spec F.unitFrame (embedHasse spec d)

/-- The additive-map form used by canonical ideal saturation. -/
def hasseAddHom (d : HasseIndex spec) : A →+ A where
  toFun := F.hasseOperator d
  map_zero' := by simp [hasseOperator]
  map_add' := by
    intro x y
    simp [hasseOperator]

@[simp] theorem hasseAddHom_apply (d : HasseIndex spec) (x : A) :
    F.hasseAddHom d x = F.hasseOperator d x := rfl

/-- Least ideal containing `I` and stable only under the genuine Hasse
operators. -/
def hasseSaturation (I : Ideal A) : Ideal A :=
  DifferentialIdealSaturation.saturation F.hasseAddHom I

/-- Contracted Hasse-only Frobenius core. -/
def core (I : Ideal A) : Ideal R :=
  (F.hasseSaturation I).comap (algebraMap R A)

/-- The Hasse-only saturation is stable under every Hasse generator. -/
theorem hasseSaturation_stable
    (I : Ideal A) (d : HasseIndex spec) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R)
        (F.hasseSaturation I))
      (F.hasseOperator d) := by
  intro x hx
  have hs := DifferentialIdealSaturation.saturation_stable
    F.hasseAddHom I d x hx
  simpa using hs

/-- The Hasse-only saturation is stable under every generator of the full
primitive packet: multiplication is automatic, Hasse stability is built in. -/
theorem hasseSaturation_fullPacket_stable
    (I : Ideal A)
    (k : IteratedHasseProduct.MultiPacketIndex spec) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R)
        (F.hasseSaturation I))
      (IteratedHasseProduct.pulledBackMultiPrimitivePacket
        (R := R) (A := A) spec F.unitFrame k) := by
  have hsound := embed_classify (R := R) spec k
  cases hclass : classify spec k with
  | inl m =>
      have hm : embedMultiplication spec m = k := by
        simpa [embedClassified, hclass] using hsound
      rw [← hm]
      rcases F.multiplicationRealization m with ⟨a, ha⟩
      rw [ha]
      exact IdealOperatorPacketDescent.leftMultiplication_stable
        (R := R) (F.hasseSaturation I) a
  | inr d =>
      have hd : embedHasse spec d = k := by
        simpa [embedClassified, hclass] using hsound
      rw [← hd]
      exact F.hasseSaturation_stable I d

/-- Hasse-only saturation already descends exactly from the base ring. -/
theorem hasseSaturation_eq_map_core (I : Ideal A) :
    F.hasseSaturation I = (F.core I).map (algebraMap R A) := by
  simpa [core] using
    (IteratedHasseProduct.ideal_eq_map_comap_of_multiPrimitive_stable
      (R := R) (A := A) spec F.unitFrame (F.hasseSaturation I)
      (F.hasseSaturation_fullPacket_stable I))

/-- A proper Hasse-only saturation yields a proper descended core. -/
theorem core_ne_top_of_saturation_ne_top
    (I : Ideal A) (hproper : F.hasseSaturation I ≠ ⊤) :
    F.core I ≠ ⊤ := by
  intro hcore
  apply hproper
  calc
    F.hasseSaturation I = (F.core I).map (algebraMap R A) :=
      F.hasseSaturation_eq_map_core I
    _ = Ideal.map (algebraMap R A) (⊤ : Ideal R) := by rw [hcore]
    _ = ⊤ := HasseSaturationDescent.map_top_algebraMap
      (R := R) (A := A)

/-- Canonical Hasse-only dichotomy on a realized finite product frame. -/
theorem hasseSaturation_dichotomy (I : Ideal A) :
    F.hasseSaturation I = ⊤ ∨
      ∃ C : Ideal R,
        C ≠ ⊤ ∧ F.hasseSaturation I = C.map (algebraMap R A) := by
  by_cases htop : F.hasseSaturation I = ⊤
  · exact Or.inl htop
  · exact Or.inr ⟨F.core I,
      F.core_ne_top_of_saturation_ne_top I htop,
      F.hasseSaturation_eq_map_core I⟩

section NoetherianAlgebra

variable [IsNoetherianRing A]

/-- Hasse-only saturation is reached by finitely many explicit closure steps. -/
theorem reaches_hasseSaturation (I : Ideal A) :
    ∃ J,
      ResolutionCompiler.Reaches
        (DifferentialIdealIteration.Step F.hasseAddHom) I J ∧
      J = F.hasseSaturation I := by
  exact DifferentialIdealIteration.reaches_saturation F.hasseAddHom I

/-- There is no infinite strict Hasse-only closure execution. -/
theorem no_infinite_hasse_closure_execution :
    ¬ ∃ f : Nat → Ideal A,
      ∀ n,
        DifferentialIdealIteration.Step F.hasseAddHom
          (f n) (f (n + 1)) := by
  exact DifferentialIdealIteration.no_infinite_closure_execution F.hasseAddHom

end NoetherianAlgebra

section NoetherianBase

variable [IsNoetherianRing R]

/-- The descended Hasse-only core is finitely generated. -/
theorem core_fg (I : Ideal A) : (F.core I).FG :=
  IsNoetherian.noetherian _

end NoetherianBase

end RealizedFrame

end

end MultiHasseOnlyDescent
end PCRLean