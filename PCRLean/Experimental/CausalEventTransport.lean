import Mathlib
import PCRLean.Experimental.CausalEventPacking

/-!
# Experimental hereditary transport of causal event anchors

The one-stage packing theorem bounds simultaneous active identities. To rule
out cloning through a geometric transform one needs a hereditary identity
witness. An anchored section equips every event with one explicit ancestor
source contained in its support. Pairwise support disjointness makes the anchor
map injective. A transport is certified only when the child anchor is exactly
the anchor of its declared parent.

The parent map of every certified transport is therefore injective. In
particular one parent cannot produce two distinct children, and the number of
active identities cannot increase through a certified transform. This is the
finite-stage no-clone theorem required by the proposed causal event cosheaf.

The file does not construct anchors or parent maps for arbitrary blowup charts;
that remains the geometric birth-realization obligation.
-/

namespace PCRLean
namespace Experimental
namespace CausalEventTransport

noncomputable section

universe u v w x

variable {Source : Type u}
variable {Parent : Type v} {Child : Type w} {Grandchild : Type x}
variable [DecidableEq Source]
variable [Fintype Source]
variable [Fintype Parent] [Fintype Child] [Fintype Grandchild]

open CausalEventPacking

/-- A packing section with one explicit conserved source anchor per event. -/
structure AnchoredSection (Event : Type*) [Fintype Event] where
  section : CausalEventPacking.Section
    (Source := Source) (Event := Event)
  anchor : Event → Source
  anchor_mem : ∀ e, anchor e ∈ section.support e

namespace AnchoredSection

variable (A : AnchoredSection (Source := Source) Parent)

/-- Disjoint support forces the explicit anchor map to be injective. -/
theorem anchor_injective : Function.Injective A.anchor := by
  intro e f hef
  apply A.section.source_owner_unique (s := A.anchor e)
  · exact A.anchor_mem e
  · simpa [hef] using A.anchor_mem f

/-- Every unanchored packing section has a noncomputable anchored refinement. -/
noncomputable def ofSection
    (C : CausalEventPacking.Section
      (Source := Source) (Event := Parent)) :
    AnchoredSection (Source := Source) Parent where
  section := C
  anchor := C.chosenSource
  anchor_mem := C.chosenSource_mem

end AnchoredSection

/-- A hereditary event transport preserves one explicit ancestor source. -/
structure Transport
    (P : AnchoredSection (Source := Source) Parent)
    (C : AnchoredSection (Source := Source) Child) where
  parent : Child → Parent
  anchor_preserved : ∀ c, C.anchor c = P.anchor (parent c)

namespace Transport

variable
    {P : AnchoredSection (Source := Source) Parent}
    {C : AnchoredSection (Source := Source) Child}
    (T : Transport P C)

/-- Anchor conservation forbids two distinct children from having one parent. -/
theorem parent_injective : Function.Injective T.parent := by
  intro c d hparent
  apply C.anchor_injective
  rw [T.anchor_preserved c, T.anchor_preserved d, hparent]

/-- No-clone theorem in equality form. -/
theorem no_clone {c d : Child} (hparent : T.parent c = T.parent d) : c = d :=
  T.parent_injective hparent

/-- A certified hereditary transform cannot increase the active event count. -/
theorem card_child_le_card_parent :
    Fintype.card Child ≤ Fintype.card Parent := by
  exact Fintype.card_le_of_injective T.parent T.parent_injective

/-- Hereditary anchor transports compose. -/
noncomputable def comp
    {G : AnchoredSection (Source := Source) Grandchild}
    (U : Transport C G) : Transport P G where
  parent := T.parent ∘ U.parent
  anchor_preserved := by
    intro g
    rw [U.anchor_preserved g, T.anchor_preserved (U.parent g)]

/-- The composite parent map is injective, hence cloning cannot occur after
any two certified transforms. -/
theorem comp_parent_injective
    {G : AnchoredSection (Source := Source) Grandchild}
    (U : Transport C G) :
    Function.Injective (T.comp U).parent :=
  (T.comp U).parent_injective

/-- Event cardinality is nonincreasing across two certified transforms. -/
theorem card_grandchild_le_card_parent
    {G : AnchoredSection (Source := Source) Grandchild}
    (U : Transport C G) :
    Fintype.card Grandchild ≤ Fintype.card Parent := by
  exact le_trans U.card_child_le_card_parent T.card_child_le_card_parent

end Transport

end

end CausalEventTransport
end Experimental
end PCRLean
