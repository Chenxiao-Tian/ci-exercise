import Mathlib
import PCRLean.DifferentialIdealSaturation

/-!
# Presentation invariance of differential ideal saturation

A canonical ideal packet must survive a change of affine presentation.  This
file proves the algebraic transport theorem: a ring equivalence conjugating two
families of additive operators carries the least stable ideal saturation on one
side to the least stable ideal saturation on the other.

A geometric application still has to show that etale coordinate changes,
changes of Rees presentation, and chart identifications induce the required
operator conjugacy.
-/

namespace PCRLean
namespace DifferentialIdealConjugacy

noncomputable section

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {ι : Type w}

/-- Operator families conjugate through a ring equivalence. -/
def Conjugate (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S) : Prop :=
  ∀ i x, e (opsR i x) = opsS i (e x)

/-- Conjugacy is symmetric. -/
theorem conjugate_symm
    (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S)
    (h : Conjugate e opsR opsS) :
    Conjugate e.symm opsS opsR := by
  intro i y
  apply e.injective
  rw [e.apply_symm_apply]
  simpa using h i (e.symm y)

/-- Mapping an ideal through a ring equivalence and back recovers it. -/
theorem map_symm_map (e : R ≃+* S) (I : Ideal R) :
    (I.map e.toRingHom).map e.symm.toRingHom = I := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

/-- A conjugacy transports stability of an ideal to stability of its image. -/
theorem stable_map
    (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S)
    (h : Conjugate e opsR opsS)
    {I : Ideal R} (hI : DifferentialIdealSaturation.Stable opsR I) :
    DifferentialIdealSaturation.Stable opsS (I.map e.toRingHom) := by
  intro i y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [← h i x]
  exact ⟨opsR i x, hI i x hx, rfl⟩

/-- One inclusion in presentation transport of canonical saturation. -/
theorem map_saturation_le
    (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S)
    (h : Conjugate e opsR opsS) (I : Ideal R) :
    (DifferentialIdealSaturation.saturation opsR I).map e.toRingHom ≤
      DifferentialIdealSaturation.saturation opsS (I.map e.toRingHom) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change e x ∈ DifferentialIdealSaturation.saturation opsS
    (I.map e.toRingHom)
  let J : Ideal S :=
    (DifferentialIdealSaturation.saturation opsR I).map e.toRingHom
  have hseed : I.map e.toRingHom ≤ J := by
    apply Ideal.map_mono
    exact DifferentialIdealSaturation.le_saturation opsR I
  have hstable : DifferentialIdealSaturation.Stable opsS J :=
    stable_map e opsR opsS h
      (DifferentialIdealSaturation.saturation_stable opsR I)
  have hmin := DifferentialIdealSaturation.saturation_le_of_le_of_stable
    opsS hseed hstable
  exact hmin ⟨x, hx, rfl⟩

/-- Canonical differential ideal saturation is invariant under conjugate
presentations. -/
theorem map_saturation_eq
    (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S)
    (h : Conjugate e opsR opsS) (I : Ideal R) :
    (DifferentialIdealSaturation.saturation opsR I).map e.toRingHom =
      DifferentialIdealSaturation.saturation opsS (I.map e.toRingHom) := by
  apply le_antisymm
  · exact map_saturation_le e opsR opsS h I
  · intro y hy
    have hback := map_saturation_le e.symm opsS opsR
      (conjugate_symm e opsR opsS h) (I.map e.toRingHom)
    have hyBack : e.symm y ∈
        (DifferentialIdealSaturation.saturation opsS
          (I.map e.toRingHom)).map e.symm.toRingHom :=
      ⟨y, hy, rfl⟩
    have hySat : e.symm y ∈ DifferentialIdealSaturation.saturation opsR I := by
      have := hback hyBack
      simpa [map_symm_map e I] using this
    exact ⟨e.symm y, hySat, e.apply_symm_apply y⟩

/-- Equal seed ideals give the same transported saturated packet. -/
theorem map_saturation_eq_of_seed_eq
    (e : R ≃+* S)
    (opsR : ι → R →+ R) (opsS : ι → S →+ S)
    (h : Conjugate e opsR opsS)
    {I I' : Ideal R} (hI : I = I') :
    (DifferentialIdealSaturation.saturation opsR I).map e.toRingHom =
      DifferentialIdealSaturation.saturation opsS (I'.map e.toRingHom) := by
  subst I'
  exact map_saturation_eq e opsR opsS h I

end

end DifferentialIdealConjugacy
end PCRLean
