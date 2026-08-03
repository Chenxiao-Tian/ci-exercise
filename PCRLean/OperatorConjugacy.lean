import Mathlib
import PCRLean.OperatorSaturation

/-!
# Presentation invariance under operator conjugacy

A canonical Hasse--Cartier packet must not depend on the chosen finite
presentation of its ancestor module. This file proves the linear-algebraic
transport theorem: conjugate operator families carry canonical operator
saturations to one another. Consequently a change of frame cannot create or
destroy the saturated trace packet.

A geometric application still has to show that changes of Rees presentation,
etale coordinates and local bundle frames induce the required conjugacies.
-/

namespace PCRLean
namespace OperatorConjugacy

noncomputable section

universe u v w x

variable {R : Type u} {D : Type v} {E : Type w} {ι : Type x}
variable [CommSemiring R]
variable [AddCommMonoid D] [Module R D]
variable [AddCommMonoid E] [Module R E]

/-- Two operator families are conjugate through a linear equivalence. -/
def Conjugate (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E) : Prop :=
  ∀ i d, e (opsD i d) = opsE i (e d)

/-- Conjugacy is symmetric. -/
theorem conjugate_symm
    (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E)
    (h : Conjugate e opsD opsE) :
    Conjugate e.symm opsE opsD := by
  intro i y
  apply e.injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [h i (e.symm y), e.apply_symm_apply]

/-- Every finite operator word is transported by a conjugacy. -/
theorem applyWord_conjugate
    (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E)
    (h : Conjugate e opsD opsE)
    (word : List ι) (d : D) :
    e (NoetherianOperatorOrbit.applyWord opsD word d) =
      NoetherianOperatorOrbit.applyWord opsE word (e d) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp only [NoetherianOperatorOrbit.applyWord]
      rw [h i, ih]

/-- A conjugacy carries the saturation of a seed submodule into the saturation
of the transported seed. -/
theorem map_saturation_le
    (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E)
    (h : Conjugate e opsD opsE)
    (N : Submodule R D) :
    (OperatorSaturation.saturation opsD N).map e.toLinearMap ≤
      OperatorSaturation.saturation opsE (N.map e.toLinearMap) := by
  rintro y ⟨d, hd, rfl⟩
  induction hd using Submodule.span_induction with
  | mem d hd =>
      rcases hd with ⟨seed, hseed, word, rfl⟩
      apply Submodule.subset_span
      refine ⟨e seed, ?_, word, ?_⟩
      · exact ⟨seed, hseed, rfl⟩
      · exact applyWord_conjugate e opsD opsE h word seed
  | zero =>
      simpa using (OperatorSaturation.saturation opsE
        (N.map e.toLinearMap)).zero_mem
  | add d₁ d₂ hd₁ hd₂ ih₁ ih₂ =>
      rw [map_add]
      exact (OperatorSaturation.saturation opsE
        (N.map e.toLinearMap)).add_mem ih₁ ih₂
  | smul a d hd ih =>
      rw [map_smul]
      exact (OperatorSaturation.saturation opsE
        (N.map e.toLinearMap)).smul_mem a ih

/-- Mapping a submodule through a linear equivalence and back recovers it. -/
theorem map_symm_map (e : D ≃ₗ[R] E) (N : Submodule R D) :
    (N.map e.toLinearMap).map e.symm.toLinearMap = N := by
  ext d
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hd
    exact ⟨e d, ⟨d, hd, rfl⟩, e.symm_apply_apply d⟩

/-- Canonical operator saturation is invariant under conjugate presentation. -/
theorem map_saturation_eq
    (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E)
    (h : Conjugate e opsD opsE)
    (N : Submodule R D) :
    (OperatorSaturation.saturation opsD N).map e.toLinearMap =
      OperatorSaturation.saturation opsE (N.map e.toLinearMap) := by
  apply le_antisymm
  · exact map_saturation_le e opsD opsE h N
  · intro y hy
    have hback := map_saturation_le e.symm opsE opsD
      (conjugate_symm e opsD opsE h) (N.map e.toLinearMap)
    have hyMap : e.symm y ∈
        (OperatorSaturation.saturation opsE
          (N.map e.toLinearMap)).map e.symm.toLinearMap :=
      ⟨y, hy, rfl⟩
    have hySat : e.symm y ∈ OperatorSaturation.saturation opsD N := by
      have := hback hyMap
      simpa [map_symm_map e N] using this
    exact ⟨e.symm y, hySat, e.apply_symm_apply y⟩

/-- The transport theorem is independent of a chosen generating list for the
seed submodule. -/
theorem map_saturation_eq_of_seed_eq
    (e : D ≃ₗ[R] E)
    (opsD : ι → Module.End R D) (opsE : ι → Module.End R E)
    (h : Conjugate e opsD opsE)
    {N N' : Submodule R D} (hN : N = N') :
    (OperatorSaturation.saturation opsD N).map e.toLinearMap =
      OperatorSaturation.saturation opsE (N'.map e.toLinearMap) := by
  subst N'
  exact map_saturation_eq e opsD opsE h N

end

end OperatorConjugacy
end PCRLean
