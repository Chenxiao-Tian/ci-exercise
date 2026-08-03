import Mathlib
import PCRLean.MonogenicFrobeniusFrame
import PCRLean.DifferentialIdealSaturation

/-!
# Canonical Hasse saturation and Frobenius cores

For an ideal in a monogenic Frobenius frame, take the least actual ideal
containing it and stable under the finite transported Hasse operators. The
saturation is canonical: it is defined by an intersection and retains no
choice of generators or order of closure operations.

The monogenic Hasse descent theorem applies automatically to this saturation.
Thus the saturated ideal is exactly the extension of its contraction to the
Frobenius base. This supplies a canonical actual base ideal, called the
Frobenius core. If the saturation is proper, then the core is proper; over a
Noetherian base it is finitely generated.
-/

namespace PCRLean
namespace HasseSaturationDescent

noncomputable section

universe u v

/-- The transported finite Hasse operator, retaining only its additive-map
structure for canonical ideal saturation. -/
def transportedHasseAddHom
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (d : Fin q) : A →+ A where
  toFun := CoordinatePacketDescent.pullbackOperator F.coord
    (FiniteHasseModel.hasse (R := R) q d)
  map_zero' := by simp
  map_add' := by
    intro x y
    simp

@[simp] theorem transportedHasseAddHom_apply
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (d : Fin q) (x : A) :
    transportedHasseAddHom F d x =
      CoordinatePacketDescent.pullbackOperator F.coord
        (FiniteHasseModel.hasse (R := R) q d) x := rfl

/-- The least ideal containing `I` and stable under every transported finite
Hasse operator. -/
def hasseSaturation
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) : Ideal A :=
  DifferentialIdealSaturation.saturation
    (transportedHasseAddHom F) I

/-- The contraction of the canonical Hasse saturation to the Frobenius base. -/
def frobeniusCore
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) : Ideal R :=
  (hasseSaturation F I).comap (algebraMap R A)

/-- The seed ideal is contained in its canonical Hasse saturation. -/
theorem le_hasseSaturation
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    I ≤ hasseSaturation F I := by
  exact DifferentialIdealSaturation.le_saturation
    (transportedHasseAddHom F) I

/-- Canonical Hasse saturation is stable under every transported Hasse
endomorphism in the sense required by monogenic Frobenius descent. -/
theorem hasseSaturation_stable
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) (d : Fin q) :
    EndomorphismGeneration.StableUnder
      (IdealEndomorphismDescent.idealSubmodule (R := R)
        (hasseSaturation F I))
      (CoordinatePacketDescent.pullbackOperator F.coord
        (FiniteHasseModel.hasse (R := R) q d)) := by
  intro x hx
  change x ∈ hasseSaturation F I at hx
  have hs := DifferentialIdealSaturation.saturation_stable
    (transportedHasseAddHom F) I d x hx
  simpa using hs

/-- The canonical Hasse saturation is exactly extended from its Frobenius
core. -/
theorem hasseSaturation_eq_map_core
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    hasseSaturation F I =
      (frobeniusCore F I).map (algebraMap R A) := by
  simpa [frobeniusCore] using
    (MonogenicFrobeniusFrame.Frame.ideal_eq_map_comap_of_hasse_stable
      F (hasseSaturation F I) (hasseSaturation_stable F I))

/-- Mapping the unit ideal along a unital ring homomorphism gives the unit
ideal. -/
theorem map_top_algebraMap
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] :
    Ideal.map (algebraMap R A) (⊤ : Ideal R) = ⊤ := by
  exact Ideal.map_top (algebraMap R A)

/-- The Frobenius core is proper whenever the Hasse saturation is proper. -/
theorem frobeniusCore_ne_top_of_saturation_ne_top
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) (hproper : hasseSaturation F I ≠ ⊤) :
    frobeniusCore F I ≠ ⊤ := by
  intro hcore
  apply hproper
  calc
    hasseSaturation F I =
        (frobeniusCore F I).map (algebraMap R A) :=
      hasseSaturation_eq_map_core F I
    _ = Ideal.map (algebraMap R A) (⊤ : Ideal R) := by rw [hcore]
    _ = ⊤ := map_top_algebraMap (R := R) (A := A)

/-- Being the unit ideal is detected exactly on the contracted Frobenius
core. -/
theorem frobeniusCore_eq_top_iff
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    frobeniusCore F I = ⊤ ↔ hasseSaturation F I = ⊤ := by
  constructor
  · intro hcore
    calc
      hasseSaturation F I =
          (frobeniusCore F I).map (algebraMap R A) :=
        hasseSaturation_eq_map_core F I
      _ = Ideal.map (algebraMap R A) (⊤ : Ideal R) := by rw [hcore]
      _ = ⊤ := map_top_algebraMap (R := R) (A := A)
  · intro hsat
    simp [frobeniusCore, hsat]

/-- Canonical saturation dichotomy: either the finite Hasse orbit generates the
unit ideal, or it yields a proper descended Frobenius core. -/
theorem hasseSaturation_dichotomy
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    hasseSaturation F I = ⊤ ∨
      ∃ C : Ideal R,
        C ≠ ⊤ ∧
        hasseSaturation F I = C.map (algebraMap R A) := by
  by_cases htop : hasseSaturation F I = ⊤
  · exact Or.inl htop
  · exact Or.inr ⟨frobeniusCore F I,
      frobeniusCore_ne_top_of_saturation_ne_top F I htop,
      hasseSaturation_eq_map_core F I⟩

/-- Over a Noetherian algebra, the canonical Hasse saturation is finitely
generated as an actual ideal. -/
theorem hasseSaturation_fg
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    (hasseSaturation F I).FG := by
  exact DifferentialIdealSaturation.saturation_fg
    (transportedHasseAddHom F) I

/-- Over a Noetherian Frobenius base, the contracted core is finitely
generated. -/
theorem frobeniusCore_fg
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    (frobeniusCore F I).FG :=
  IsNoetherian.noetherian _

/-- A finite actual generator set exists for the descended Frobenius core. -/
theorem exists_finite_frobeniusCore_generators
    {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R]
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame (R := R) (A := A) q t)
    (I : Ideal A) :
    ∃ s : Finset R,
      frobeniusCore F I = Ideal.span (s : Set R) := by
  rcases frobeniusCore_fg F I with ⟨s, hs⟩
  exact ⟨s, hs.symm⟩

end

end HasseSaturationDescent
end PCRLean
