import Mathlib
import PCRLean.Experimental.MinimalHybridCentre

/-!
# Experimental canonical closure of minimal hybrid centres

Cardinality-minimal permissible component families need not be unique. Choosing
one family by classical choice can break a geometric symmetry.  Since the
component index type is finite, take the union of *all* cardinality-minimal
permissible families and join all components appearing in that union.

Every minimal permissible family is contained in this canonical support.
Marked permissibility is monotone under enlargement of the centre ideal, so the
canonical closure remains permissible. The construction removes tie-breaking
from the finite component-synthesis layer.

The canonical closure may contain more components than a minimal family. This
file does not prove regularity, passive safety, boundary transversality, or
nonidentity of the enlarged centre. In the separate linear-subspace chamber,
finite joins remain regular.
-/

namespace PCRLean
namespace Experimental
namespace CanonicalHybridClosure

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

open MinimalHybridCentre

/-- A permissible family whose cardinality is no larger than that of any other
permissible family. -/
def IsCardinalMinimal
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R)
    (selected : Finset ι) : Prop :=
  Acceptable P component selected ∧
    ∀ candidate : Finset ι,
      Acceptable P component candidate →
        selected.card ≤ candidate.card

/-- Finite collection of all cardinality-minimal permissible families. -/
noncomputable def minimalFamilies
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (IsCardinalMinimal P component)

/-- Symmetry-safe support obtained by taking the union of every minimal
permissible family. -/
noncomputable def canonicalSelected
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R) : Finset ι := by
  classical
  exact (minimalFamilies P component).biUnion id

/-- Actual ideal obtained from the canonical selected support. -/
noncomputable def canonicalCentre
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R) : Ideal R :=
  combinedCentre component (canonicalSelected P component)

namespace MinimalCertificate

variable {P : MarkedIdeal.Packet R} {component : ι → Ideal R}

/-- Every cardinality-minimal certificate occurs in the finite family used by
the canonical construction. -/
theorem selected_mem_minimalFamilies
    (C : MinimalCertificate P component) :
    C.selected ∈ minimalFamilies P component := by
  classical
  rw [minimalFamilies, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨C.acceptable, C.cardinalMinimal⟩⟩

/-- The support of every minimal certificate is contained in the canonical
support. -/
theorem selected_subset_canonicalSelected
    (C : MinimalCertificate P component) :
    C.selected ⊆ canonicalSelected P component := by
  classical
  intro i hi
  rw [canonicalSelected, Finset.mem_biUnion]
  exact ⟨C.selected, C.selected_mem_minimalFamilies, hi⟩

/-- The ideal of every minimal permissible hybrid is contained in the canonical
closure ideal. -/
theorem combinedCentre_le_canonicalCentre
    (C : MinimalCertificate P component) :
    combinedCentre component C.selected ≤
      canonicalCentre P component := by
  unfold canonicalCentre combinedCentre
  exact Finset.sup_mono C.selected_subset_canonicalSelected

/-- The symmetry-safe closure remains marked-permissible. -/
theorem canonical_acceptable
    (C : MinimalCertificate P component) :
    Acceptable P component (canonicalSelected P component) := by
  unfold Acceptable
  exact MarkedIdeal.permissible_mono C.acceptable
    C.combinedCentre_le_canonicalCentre

end MinimalCertificate

/-- If the full component family is permissible, the canonical symmetry-safe
closure is permissible. No arbitrary minimal-family choice appears in the
conclusion. -/
theorem canonical_acceptable_of_full
    (P : MarkedIdeal.Packet R)
    (component : ι → Ideal R)
    (hfull : Acceptable P component Finset.univ) :
    Acceptable P component (canonicalSelected P component) := by
  obtain ⟨C⟩ := exists_minimalCertificate P component hfull
  exact C.canonical_acceptable

/-- Every component occurring in any minimal permissible family occurs in the
canonical support. -/
theorem mem_canonicalSelected_of_mem_minimal
    {P : MarkedIdeal.Packet R}
    {component : ι → Ideal R}
    {selected : Finset ι}
    (hminimal : IsCardinalMinimal P component selected)
    {i : ι} (hi : i ∈ selected) :
    i ∈ canonicalSelected P component := by
  classical
  rw [canonicalSelected, Finset.mem_biUnion]
  refine ⟨selected, ?_, hi⟩
  rw [minimalFamilies, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hminimal⟩

end

end CanonicalHybridClosure
end Experimental
end PCRLean
