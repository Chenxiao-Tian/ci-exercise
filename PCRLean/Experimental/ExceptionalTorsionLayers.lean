import Mathlib

/-!
# Nested exceptional-torsion layers

On one exceptional chart of a centre-enriched blowup, let

* `inherited` be the image in the associated graded of the exceptional torsion
  already removed from the ambient module; and
* `purified` be the full exceptional-power torsion of the associated graded.

The first layer is contained in the second.  Their quotient is the local
purification--grading interchange defect.  This file deliberately avoids
choosing one defect element: it records the exact clean/defect coverage and the
existence of a witness precisely when the two layers differ.

The scheme-level X038 theorem must identify these layers with
`gr_L^ind(H^0_(u)(N))` and `H^0_(u)(gr_L(N))`, prove Artin--Rees finiteness and
flat-base-change compatibility, and realize the quotient as an exceptional
coherent packet.  None of those geometric conclusions is asserted here.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalTorsionLayers

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The inherited exceptional-torsion layer and the full purified layer. -/
structure Layers where
  inherited : Submodule R M
  purified : Submodule R M
  inherited_le_purified : inherited ≤ purified

namespace Layers

variable (L : Layers (R := R) (M := M))

/-- A concrete witness that purification after grading removes more than
purification before grading. -/
def DefectWitness :=
  {x : M // x ∈ L.purified ∧ x ∉ L.inherited}

/-- Equality of the two torsion layers rules out every defect witness. -/
theorem no_witness_of_eq
    (h : L.inherited = L.purified) :
    ¬ Nonempty L.DefectWitness := by
  rintro ⟨x⟩
  exact x.property.2 (by simpa [h] using x.property.1)

/-- If the nested layers are distinct, the larger layer contains a witness
outside the inherited layer. -/
theorem exists_witness_of_ne
    (h : L.inherited ≠ L.purified) :
    Nonempty L.DefectWitness := by
  classical
  have hex : ∃ x : M, x ∈ L.purified ∧ x ∉ L.inherited := by
    by_contra hnone
    push_neg at hnone
    apply h
    apply le_antisymm L.inherited_le_purified
    intro x hx
    exact hnone x hx
  obtain ⟨x, hxU, hxH⟩ := hex
  exact ⟨⟨x, hxU, hxH⟩⟩

/-- Exact clean/defect equivalence. -/
theorem witness_nonempty_iff_ne :
    Nonempty L.DefectWitness ↔ L.inherited ≠ L.purified := by
  constructor
  · intro hw hEq
    exact L.no_witness_of_eq hEq hw
  · exact L.exists_witness_of_ne

/-- The choice-free status of the local interchange layer. -/
inductive Status : Type (max u v) where
  | clean (eq_layers : L.inherited = L.purified)
  | defect (witness : Nonempty L.DefectWitness)

/-- Every nested pair lies in exactly one of the clean and defect chambers. -/
noncomputable def classify : L.Status := by
  classical
  by_cases h : L.inherited = L.purified
  · exact Status.clean h
  · exact Status.defect (L.exists_witness_of_ne h)

end Layers

end

end ExceptionalTorsionLayers
end Experimental
end PCRLean
