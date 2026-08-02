import Mathlib
import PCRLean.MonogenicFrobeniusFrame
import PCRLean.DifferentialIdealSaturation

/-!
# Canonical Hasse saturation and Frobenius cores

For an ideal in a monogenic Frobenius frame, take the least actual ideal
containing it and stable under the finite transported Hasse operators.  The
saturation is canonical: it is defined by an intersection and retains no
choice of generators or order of closure operations.

The monogenic Hasse descent theorem applies automatically to this saturation.
Thus the saturated ideal is exactly the extension of its contraction to the
Frobenius base.  This supplies a canonical actual base ideal, called the
Frobenius core.  If the saturation is proper, then the core is proper; over a
Noetherian base it is finitely generated.

The resulting dichotomy is finite and intrinsic on the chosen Frobenius chart:
either the Hasse orbit saturates to the unit ideal, or it produces a proper
finitely generated descended core.
-/

namespace PCRLean
namespace HasseSaturationDescent

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable {q : Nat} {t : R}

abbrev Frame := MonogenicFrobeniusFrame.Frame

namespace Frame

variable (F : Frame (R := R) (A := A) q t)

/-- The transported finite Hasse operator, retaining only its additive-map
structure for canonical ideal saturation. -/
def transportedHasseAddHom (d : Fin q) : A →+ A :=
  (CoordinatePacketDescent.pullbackOperator F.coord
    (FiniteHasseModel.hasse (R := R) q d)).toAddHom

/-- The least ideal containing `I` and stable under every transported finite
Hasse operator. -/
def hasseSaturation (I : Ideal A) : Ideal A :=
  DifferentialIdealSaturation.saturation F.transportedHasseAddHom I

/-- The contraction of the canonical Hasse saturation to the Frobenius base. -/
def frobeniusCore (I : Ideal A) : Ideal R :=
  (F.hasseSaturation I).comap (algebraMap R A)

/-- The seed ideal is contained in its canonical Hasse saturation. -/
theorem le_hasseSaturation (I : Ideal A) :
    I ≤ F.hasseSaturation I := by
  exact DifferentialIdealSaturation.le_saturation
    F.transportedHasseAddHom I

/-- Canonical Hasse saturation is stable under every transported Hasse
endomorphism in the sense required by monogenic Frobenius descent. -/
theorem hasseSaturation_stable (I : Ideal A) (d : Fin q) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R)
        (F.hasseSaturation I))
      (CoordinatePacketDescent.pullbackOperator F.coord
        (FiniteHasseModel.hasse (R := R) q d)) := by
  intro x hx
  change F.transportedHasseAddHom d x ∈ F.hasseSaturation I
  exact DifferentialIdealSaturation.saturation_stable
    F.transportedHasseAddHom I d x hx

/-- The canonical Hasse saturation is exactly extended from its Frobenius
core. -/
theorem hasseSaturation_eq_map_core (I : Ideal A) :
    F.hasseSaturation I =
      (F.frobeniusCore I).map (algebraMap R A) := by
  simpa [frobeniusCore] using
    F.ideal_eq_map_comap_of_hasse_stable
      (F.hasseSaturation I) (F.hasseSaturation_stable I)

/-- The Frobenius core is proper whenever the Hasse saturation is proper. -/
theorem frobeniusCore_ne_top_of_saturation_ne_top
    (I : Ideal A) (hproper : F.hasseSaturation I ≠ ⊤) :
    F.frobeniusCore I ≠ ⊤ := by
  intro hcore
  apply hproper
  calc
    F.hasseSaturation I =
        (F.frobeniusCore I).map (algebraMap R A) :=
      F.hasseSaturation_eq_map_core I
    _ = ⊤ := by simp [hcore]

/-- Being the unit ideal is detected exactly on the contracted Frobenius
core. -/
theorem frobeniusCore_eq_top_iff (I : Ideal A) :
    F.frobeniusCore I = ⊤ ↔ F.hasseSaturation I = ⊤ := by
  constructor
  · intro hcore
    calc
      F.hasseSaturation I =
          (F.frobeniusCore I).map (algebraMap R A) :=
        F.hasseSaturation_eq_map_core I
      _ = ⊤ := by simp [hcore]
  · intro hsat
    simp [frobeniusCore, hsat]

/-- Canonical saturation dichotomy: either the finite Hasse orbit generates the
unit ideal, or it yields a proper descended Frobenius core. -/
theorem hasseSaturation_dichotomy (I : Ideal A) :
    F.hasseSaturation I = ⊤ ∨
      ∃ C : Ideal R,
        C ≠ ⊤ ∧
        F.hasseSaturation I = C.map (algebraMap R A) := by
  by_cases htop : F.hasseSaturation I = ⊤
  · exact Or.inl htop
  · exact Or.inr ⟨F.frobeniusCore I,
      F.frobeniusCore_ne_top_of_saturation_ne_top I htop,
      F.hasseSaturation_eq_map_core I⟩

section Noetherian

variable [IsNoetherianRing A]

/-- Over a Noetherian algebra, the canonical Hasse saturation is finitely
generated as an actual ideal. -/
theorem hasseSaturation_fg (I : Ideal A) :
    (F.hasseSaturation I).FG := by
  exact DifferentialIdealSaturation.saturation_fg
    F.transportedHasseAddHom I

end Noetherian

section NoetherianBase

variable [IsNoetherianRing R]

/-- Over a Noetherian Frobenius base, the contracted core is finitely
generated. -/
theorem frobeniusCore_fg (I : Ideal A) :
    (F.frobeniusCore I).FG :=
  IsNoetherian.noetherian _

/-- A finite actual generator set exists for the descended Frobenius core. -/
theorem exists_finite_frobeniusCore_generators (I : Ideal A) :
    ∃ s : Finset R,
      F.frobeniusCore I = Ideal.span (s : Set R) := by
  rcases F.frobeniusCore_fg I with ⟨s, hs⟩
  exact ⟨s, hs.symm⟩

end NoetherianBase

end Frame

end

end HasseSaturationDescent
end PCRLean
