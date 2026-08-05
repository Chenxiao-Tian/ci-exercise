import Mathlib

/-!
# Minimal strata are disjoint or contained

A finite wonderful arrangement is represented here by a finite family of
finite point sets closed under binary intersection.  If `D` is a minimal
nonempty member, then for every other member `C`, either `D ∩ C` is empty or
`D ⊆ C`.

This is the exact combinatorial skeleton behind deepest-first serialization:
a minimal current stratum interacts with every remaining stratum only through
the disjoint case or the nested regular-flag case.  The file proves no
scheme-theoretic intersection, regularity, blowup, or resolution theorem.
-/

namespace PCRLean
namespace Experimental
namespace MinimalStratumNesting

noncomputable section

universe u

variable {α : Type u} [DecidableEq α]

/-- Binary intersection closure of a finite family of finite strata. -/
def IntersectionClosed (family : Finset (Finset α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ∩ B ∈ family

/-- `D` is a minimal nonempty stratum under inclusion. -/
def MinimalNonempty
    (family : Finset (Finset α)) (D : Finset α) : Prop :=
  D ∈ family ∧ D.Nonempty ∧
    ∀ S ∈ family, S.Nonempty → S ⊆ D → D ⊆ S

/-- A minimal nonempty stratum is either disjoint from or contained in every
other stratum. -/
theorem disjoint_or_subset
    {family : Finset (Finset α)} {D C : Finset α}
    (hclosed : IntersectionClosed family)
    (hD : MinimalNonempty family D)
    (hC : C ∈ family) :
    Disjoint D C ∨ D ⊆ C := by
  classical
  by_cases hempty : D ∩ C = ∅
  · left
    exact Finset.disjoint_iff_inter_eq_empty.mpr hempty
  · right
    have hmem : D ∩ C ∈ family := hclosed D hD.1 C hC
    have hnonempty : (D ∩ C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    have hsubD : D ∩ C ⊆ D := Finset.inter_subset_left
    have hDsub : D ⊆ D ∩ C := hD.2.2 (D ∩ C) hmem hnonempty hsubD
    intro x hx
    exact (Finset.mem_inter.mp (hDsub hx)).2

/-- In the non-disjoint chamber the intersection equals the minimal stratum. -/
theorem inter_eq_left_of_not_disjoint
    {family : Finset (Finset α)} {D C : Finset α}
    (hclosed : IntersectionClosed family)
    (hD : MinimalNonempty family D)
    (hC : C ∈ family)
    (hnot : ¬ Disjoint D C) :
    D ∩ C = D := by
  rcases disjoint_or_subset hclosed hD hC with hdisj | hsub
  · exact False.elim (hnot hdisj)
  · exact Finset.inter_eq_left.mpr hsub

end

end MinimalStratumNesting
end Experimental
end PCRLean
