import Mathlib
import PCRLean.GenerationalRank
import PCRLean.Experimental.CausalEventPacking

/-!
# Experimental causal event ledger

The earlier packing theorem bounds active identities at one stage. This file
adds dynamics. A state stores actual finite supports in one fixed finite
ancestor-source set. A genuine birth inserts a nonempty support disjoint from
all currently used sources. Hence the support lies inside the current unused
ledger, and the unused-source cardinality strictly decreases.

Merges preserve the unused ledger and lower the number of active support
blocks. Internal cleanup preserves both outer coordinates and lowers a local
height. Thus the abstract `GenRank` is computed from actual source data, rather
than supplied as arbitrary natural numbers.

The remaining geometric obligation is to assign such hereditary supports to
every birth created by Frobenius/Fitting transforms and prove that localization,
chart change, cleaning, and reentry never clone a source.
-/

namespace PCRLean
namespace Experimental
namespace CausalEventLedger

noncomputable section

universe u

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- One finite causal-ledger stage. `active` stores the actual support blocks of
all currently active identities. -/
structure State where
  active : Finset (Finset Source)
  cleanupHeight : Nat
  deriving DecidableEq

namespace State

/-- Ancestor sources currently owned by some active identity. -/
def used (S : State (Source := Source)) : Finset Source :=
  S.active.biUnion id

/-- Sources not yet consumed by an active identity. -/
def unused (S : State (Source := Source)) : Finset Source :=
  Finset.univ \ S.used

/-- Concrete causal rank extracted from the ledger. -/
def rank (S : State (Source := Source)) : GenRank where
  unusedCarrier := S.unused.card
  activeIdentities := S.active.card
  cleanupHeight := S.cleanupHeight

end State

/-- A financed birth inserts one nonempty support disjoint from every source
already in use. -/
structure Birth
    (parent child : State (Source := Source)) where
  newSupport : Finset Source
  new_nonempty : newSupport.Nonempty
  disjoint_used : Disjoint newSupport parent.used
  child_active : child.active = insert newSupport parent.active

namespace Birth

variable {parent child : State (Source := Source)}
    (B : Birth parent child)

/-- Every source charged to the new identity was previously unused. -/
theorem newSupport_subset_unused :
    B.newSupport ⊆ parent.unused := by
  intro s hs
  have hsNotUsed : s ∉ parent.used := by
    intro hsUsed
    exact (Finset.disjoint_left.mp B.disjoint_used) hs hsUsed
  simp [State.unused, hsNotUsed]

/-- The child used set is obtained by adjoining the new support. -/
theorem used_child :
    child.used = B.newSupport ∪ parent.used := by
  ext s
  simp [State.used, B.child_active]

/-- The child unused set is the old unused set with the new support removed. -/
theorem unused_child :
    child.unused = parent.unused \ B.newSupport := by
  ext s
  simp [State.unused, B.used_child, and_left_comm, and_comm, and_assoc]

/-- A genuine financed birth strictly consumes the finite ancestor-source
ledger. -/
theorem unused_card_decreases :
    child.unused.card < parent.unused.card := by
  rw [B.unused_child]
  exact Finset.card_lt_card
    (Finset.sdiff_ssubset B.newSupport_subset_unused B.new_nonempty)

end Birth

/-- Accepted ledger moves. Birth decrease is derived from actual supports;
merge and cleanup carry the exact conservation equations their geometric
realization must prove. -/
inductive Step :
    State (Source := Source) → State (Source := Source) → Prop
  | birth {parent child}
      (B : Birth parent child) : Step parent child
  | sourceMerge {parent child}
      (hunused : child.unused = parent.unused)
      (hactive : child.active.card < parent.active.card) : Step parent child
  | cleanup {parent child}
      (hunused : child.unused = parent.unused)
      (hactive : child.active.card = parent.active.card)
      (hcleanup : child.cleanupHeight < parent.cleanupHeight) :
      Step parent child

namespace Step

/-- Every accepted causal-ledger move strictly lowers the concrete generation
rank. -/
theorem decreases {parent child : State (Source := Source)}
    (h : Step parent child) :
    GenRank.Lt child.rank parent.rank := by
  cases h with
  | birth B =>
      exact Or.inl B.unused_card_decreases
  | sourceMerge hunused hactive =>
      exact Or.inr ⟨congrArg Finset.card hunused, Or.inl hactive⟩
  | cleanup hunused hactive hcleanup =>
      exact Or.inr
        ⟨congrArg Finset.card hunused,
          Or.inr ⟨hactive, hcleanup⟩⟩

/-- No infinite execution can satisfy the actual finite-source ledger protocol. -/
theorem noInfinitePath :
    ¬ ∃ f : Nat → State (Source := Source),
      ∀ n, Step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact noInfiniteDescending GenRank.wellFounded
    (fun n => (f n).rank)
    (fun n => decreases (hf n))

end Step

end

end CausalEventLedger
end Experimental
end PCRLean
