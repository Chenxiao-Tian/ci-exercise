import Mathlib
import PCRLean.SourcePartition

/-!
# Experimental causal event packing

A jump-capable identity carries a nonempty finite support in one fixed finite
ancestor-source set. Distinct active identities must have disjoint supports.
This is the one-stage packing shadow of the proposed causal event cosheaf.

The theorem proves a strict conservation law: the number of simultaneously
active jump-capable identities cannot exceed the number of fixed ancestor
sources. It rules out independent cloning at one state, but it does not yet
construct supports for arbitrary geometric births or prove hereditary transport
through every chart.
-/

namespace PCRLean
namespace Experimental
namespace CausalEventPacking

noncomputable section

universe u v

variable {Source : Type u} {Event : Type v}
variable [Fintype Source] [Fintype Event]
variable [DecidableEq Source]

/-- One finite stage of the proposed causal event cosheaf. -/
structure Section where
  support : Event → Finset Source
  support_nonempty : ∀ e, (support e).Nonempty
  support_disjoint : ∀ e f, e ≠ f → Disjoint (support e) (support f)

namespace Section

variable (C : Section (Source := Source) (Event := Event))

/-- Choose one conserved ancestor source from every active identity. -/
def chosenSource (e : Event) : Source :=
  (C.support_nonempty e).choose

/-- The chosen source really belongs to the event support. -/
theorem chosenSource_mem (e : Event) :
    C.chosenSource e ∈ C.support e :=
  (C.support_nonempty e).choose_spec

/-- One fixed ancestor source cannot be owned by two distinct active events. -/
theorem source_owner_unique
    {e f : Event} {s : Source}
    (he : s ∈ C.support e) (hf : s ∈ C.support f) : e = f := by
  by_contra hef
  exact (Finset.disjoint_left.mp (C.support_disjoint e f hef)) he hf

/-- Choosing one source in each support embeds active events into the fixed
ancestor-source set. -/
theorem chosenSource_injective : Function.Injective C.chosenSource := by
  intro e f hef
  apply C.source_owner_unique (s := C.chosenSource e)
  · exact C.chosenSource_mem e
  · simpa [hef] using C.chosenSource_mem f

/-- Finite-source packing bound: active jump-capable identities are bounded by
fixed ancestor sources. -/
include C in
theorem card_events_le_card_sources :
    Fintype.card Event ≤ Fintype.card Source := by
  exact Fintype.card_le_of_injective
    (fun e => chosenSource C e)
    (chosenSource_injective C)

/-- If every ancestor source is already assigned, a new disjoint nonempty event
cannot be inserted without merging or releasing an old support. -/
theorem no_fresh_disjoint_support_of_cover
    (hcover : Finset.univ.biUnion C.support = Finset.univ)
    (newSupport : Finset Source)
    (hnew : newSupport.Nonempty)
    (hdisj : ∀ e, Disjoint newSupport (C.support e)) : False := by
  rcases hnew with ⟨s, hs⟩
  have hsAll : s ∈ Finset.univ.biUnion C.support := by
    rw [hcover]
    simp
  simp only [Finset.mem_biUnion] at hsAll
  rcases hsAll with ⟨e, heUniv, hse⟩
  exact (Finset.disjoint_left.mp (hdisj e)) hs hse

end Section

end

end CausalEventPacking
end Experimental
end PCRLean
