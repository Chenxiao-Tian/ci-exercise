import Mathlib
import PCRLean.MarkedIdeal

/-!
# Experimental finite minimal hybrid-centre compiler

Suppose a finite family of actual ideal components has a marked-permissible
join. Components may represent intrinsic packet kernels, Frobenius roots,
ordinary/Hasse defects, boundary corrections, or owner corrections.

This file proves that one can select a cardinality-minimal permissible
subfamily. Every selected component is indispensable: deleting it destroys
permissibility. The result formalizes the finite synthesis step suggested by
the cusp `y^p-x^(p+1)`, where neither `(x)` nor `(y)` is permissible but
`(x,y)` is.

The theorem does not prove that the selected join is regular, contained in the
singular locus, owner-safe, boundary-transverse, or hereditary under blowup.
Those remain separate geometric gates.
-/

namespace PCRLean
namespace Experimental
namespace MinimalHybridCentre

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Join of a finite selected family of actual ideal components. -/
def combinedCentre (component : ι → Ideal R) (selected : Finset ι) : Ideal R :=
  selected.sup component

/-- A selected component family is acceptable at the marked-power gate. -/
def Acceptable (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R) (selected : Finset ι) : Prop :=
  MarkedIdeal.Permissible P (combinedCentre component selected)

/-- Certificate that a permissible hybrid uses the smallest possible number of
components. -/
structure MinimalCertificate
    (P : MarkedIdeal.Packet R) (component : ι → Ideal R) where
  selected : Finset ι
  acceptable : Acceptable P component selected
  cardinalMinimal : ∀ candidate : Finset ι,
    Acceptable P component candidate → selected.card ≤ candidate.card

namespace MinimalCertificate

variable {P : MarkedIdeal.Packet R} {component : ι → Ideal R}

/-- No selected component can be erased while retaining marked permissibility. -/
theorem erase_not_acceptable
    (C : MinimalCertificate P component)
    {i : ι} (hi : i ∈ C.selected) :
    ¬ Acceptable P component (C.selected.erase i) := by
  intro herase
  have hle := C.cardinalMinimal (C.selected.erase i) herase
  have hlt : (C.selected.erase i).card < C.selected.card :=
    Finset.card_erase_lt_of_mem hi
  omega

/-- Every selected component is indispensable. -/
theorem all_components_indispensable
    (C : MinimalCertificate P component) :
    ∀ i ∈ C.selected,
      ¬ Acceptable P component (C.selected.erase i) := by
  intro i hi
  exact C.erase_not_acceptable hi

end MinimalCertificate

/-- If the join of all named components is permissible, a cardinality-minimal
permissible hybrid subfamily exists. -/
theorem exists_minimalCertificate
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R)
    (hfull : Acceptable P component Finset.univ) :
    Nonempty (MinimalCertificate P component) := by
  classical
  let property : Nat → Prop := fun n =>
    ∃ selected : Finset ι,
      selected.card = n ∧ Acceptable P component selected
  have hex : ∃ n, property n := by
    exact ⟨Finset.univ.card, Finset.univ, rfl, hfull⟩
  obtain ⟨selected, hcard, hacceptable⟩ := Nat.find_spec hex
  refine ⟨{
    selected := selected
    acceptable := hacceptable
    cardinalMinimal := ?_
  }⟩
  intro candidate hcandidate
  have hproperty : property candidate.card :=
    ⟨candidate, rfl, hcandidate⟩
  have hmin : Nat.find hex ≤ candidate.card :=
    Nat.find_min' hex hproperty
  omega

/-- Expanded existence theorem exposing both global cardinal minimality and
local indispensability. -/
theorem exists_minimal_permissible_hybrid
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R)
    (hfull : Acceptable P component Finset.univ) :
    ∃ selected : Finset ι,
      Acceptable P component selected ∧
      (∀ candidate : Finset ι,
        Acceptable P component candidate →
          selected.card ≤ candidate.card) ∧
      (∀ i ∈ selected,
        ¬ Acceptable P component (selected.erase i)) := by
  obtain ⟨C⟩ := exists_minimalCertificate P component hfull
  exact ⟨C.selected, C.acceptable, C.cardinalMinimal,
    C.all_components_indispensable⟩

/-- If neither the empty family nor any singleton is permissible, every
cardinality-minimal permissible hybrid necessarily uses at least two
components. -/
theorem minimal_card_ge_two_of_empty_and_singletons_fail
    {P : MarkedIdeal.Packet R}
    {component : ι → Ideal R}
    (C : MinimalCertificate P component)
    (hempty : ¬ Acceptable P component ∅)
    (hsingleton : ∀ i : ι,
      ¬ Acceptable P component {i}) :
    2 ≤ C.selected.card := by
  by_contra hnot
  have hcases : C.selected.card = 0 ∨ C.selected.card = 1 := by
    omega
  rcases hcases with hzero | hone
  · have hsel : C.selected = ∅ := Finset.card_eq_zero.mp hzero
    exact hempty (hsel ▸ C.acceptable)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    exact hsingleton i (hi ▸ C.acceptable)

end

end MinimalHybridCentre
end Experimental
end PCRLean
