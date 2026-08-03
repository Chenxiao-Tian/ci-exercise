import Mathlib
import PCRLean.NoetherianOperatorOrbit

/-!
# Presentation invariance of operator-orbit packets

A finite Hasse--Cartier packet is useful only if it is independent of a chosen
linear presentation.  This file proves the exact linearized statement: an
operator-conjugating linear equivalence carries every finite operator word,
the full raw orbit, and the generated orbit module to the corresponding data
in the new presentation.

The geometric problem of producing such equivalences from changes of marked
presentation remains separate.
-/

namespace PCRLean
namespace OperatorOrbitEquiv

noncomputable section

universe u v w x

variable {R : Type u} {D : Type v} {D' : Type w} {ι : Type x}
variable [CommSemiring R]
variable [AddCommMonoid D] [Module R D]
variable [AddCommMonoid D'] [Module R D']

/-- An equivalence intertwines two operator families. -/
def Intertwines (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D') : Prop :=
  ∀ i d, e (ops i d) = ops' i (e d)

/-- Intertwining propagates from generators to every finite operator word. -/
theorem applyWord_intertwines
    (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (h : Intertwines e ops ops')
    (word : List ι) (d : D) :
    e (NoetherianOperatorOrbit.applyWord ops word d) =
      NoetherianOperatorOrbit.applyWord ops' word (e d) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      simp only [NoetherianOperatorOrbit.applyWord_cons]
      rw [h i, ih]

/-- The inverse equivalence intertwines the operator families in the reverse
direction. -/
theorem symm_intertwines
    (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (h : Intertwines e ops ops') :
    Intertwines e.symm ops' ops := by
  intro i d'
  apply e.injective
  simpa using h i (e.symm d')

/-- A raw orbit element maps to a raw orbit element in the new presentation. -/
theorem map_mem_orbitSet
    (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (h : Intertwines e ops ops') (seed : D)
    {d : D} (hd : d ∈ NoetherianOperatorOrbit.orbitSet ops seed) :
    e d ∈ NoetherianOperatorOrbit.orbitSet ops' (e seed) := by
  rcases hd with ⟨word, rfl⟩
  exact ⟨word, (applyWord_intertwines e ops ops' h word seed).symm⟩

/-- The full operator-orbit submodule is carried exactly to the orbit module
in the equivalent presentation. -/
theorem map_orbitModule_eq
    (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (h : Intertwines e ops ops') (seed : D) :
    (NoetherianOperatorOrbit.orbitModule ops seed).map e.toLinearMap =
      NoetherianOperatorOrbit.orbitModule ops' (e seed) := by
  apply le_antisymm
  · rintro y ⟨d, hd, rfl⟩
    induction hd using Submodule.span_induction with
    | mem d hd =>
        exact Submodule.subset_span (map_mem_orbitSet e ops ops' h seed hd)
    | zero =>
        simpa using (NoetherianOperatorOrbit.orbitModule ops' (e seed)).zero_mem
    | add a b ha hb hma hmb =>
        rw [map_add]
        exact (NoetherianOperatorOrbit.orbitModule ops' (e seed)).add_mem hma hmb
    | smul a d hd hmd =>
        rw [map_smul]
        exact (NoetherianOperatorOrbit.orbitModule ops' (e seed)).smul_mem a hmd
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨word, rfl⟩
        refine ⟨NoetherianOperatorOrbit.applyWord ops word seed, ?_, ?_⟩
        · exact Submodule.subset_span ⟨word, rfl⟩
        · exact applyWord_intertwines e ops ops' h word seed
    | zero =>
        exact (NoetherianOperatorOrbit.orbitModule ops seed).map_zero
    | add a b ha hb hma hmb =>
        exact (NoetherianOperatorOrbit.orbitModule ops seed).map_add hma hmb
    | smul a d hd hmd =>
        exact (NoetherianOperatorOrbit.orbitModule ops seed).map_smul a hmd

/-- Finite generation of the operator packet is invariant under an
operator-conjugating change of presentation. -/
theorem fg_orbit_iff
    (e : D ≃ₗ[R] D')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (h : Intertwines e ops ops') (seed : D) :
    (NoetherianOperatorOrbit.orbitModule ops seed).FG ↔
      (NoetherianOperatorOrbit.orbitModule ops' (e seed)).FG := by
  rw [← map_orbitModule_eq e ops ops' h seed]
  exact e.toLinearMap.fg_map_iff

end

end OperatorOrbitEquiv
end PCRLean
