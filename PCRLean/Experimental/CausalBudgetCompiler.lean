import Mathlib
import PCRLean.GenerationalRank

/-!
# Experimental causal source-budget compiler

A geometric state records the finite set of ancestor sources already consumed,
the number of active identities, and an inner cleanup height. A financed birth
must insert a genuinely fresh source. Merges and cleanup steps keep the source
ledger fixed and lower the active count, while macro-internal steps keep the
first two coordinates fixed and lower cleanup height.

The concrete state maps to the already verified three-level `GenRank`. Every
accepted transition strictly lowers that rank, so no infinite execution is
possible.

This is a termination compiler, not the missing geometric realization theorem.
An application to positive-characteristic resolution must still prove that
every actual birth consumes a fresh ancestor source and that every remaining
transition is one of the certified local drops.
-/

namespace PCRLean
namespace Experimental
namespace CausalBudgetCompiler

noncomputable section

universe u

variable {Source : Type u} [Fintype Source] [DecidableEq Source]

/-- Concrete state carrying the consumed-source ledger and two local ranks. -/
structure State where
  usedSources : Finset Source
  activeIdentities : Nat
  cleanupHeight : Nat
  deriving DecidableEq

/-- Remaining source budget followed by active and cleanup ranks. -/
def rank (s : State (Source := Source)) : GenRank where
  unusedCarrier := Fintype.card Source - s.usedSources.card
  activeIdentities := s.activeIdentities
  cleanupHeight := s.cleanupHeight

/-- Geometric moves accepted by the concrete source-budget compiler. -/
inductive Step : State (Source := Source) → State (Source := Source) → Prop
  | financedBirth (parent child : State (Source := Source)) (source : Source)
      (hused : child.usedSources = insert source parent.usedSources)
      (hfresh : source ∉ parent.usedSources) : Step parent child
  | sourceMerge (parent child : State (Source := Source))
      (hused : child.usedSources = parent.usedSources)
      (hactive : child.activeIdentities < parent.activeIdentities) : Step parent child
  | cleanup (parent child : State (Source := Source))
      (hused : child.usedSources = parent.usedSources)
      (hactive : child.activeIdentities < parent.activeIdentities) : Step parent child
  | macroInternal (parent child : State (Source := Source))
      (hused : child.usedSources = parent.usedSources)
      (hactive : child.activeIdentities = parent.activeIdentities)
      (hcleanup : child.cleanupHeight < parent.cleanupHeight) : Step parent child

namespace Step

/-- A fresh source exists outside the old ledger, so the old ledger has
strictly smaller cardinality than the full source set. -/
theorem usedSources_card_lt
    (parent : State (Source := Source)) {source : Source}
    (hfresh : source ∉ parent.usedSources) :
    parent.usedSources.card < Fintype.card Source := by
  have hproper :
      parent.usedSources ⊂ (Finset.univ : Finset Source) := by
    constructor
    · exact Finset.subset_univ _
    · intro hreverse
      exact hfresh (hreverse (by simp))
  simpa using Finset.card_lt_card hproper

/-- Every concrete accepted transition strictly lowers the verified generation
rank. -/
theorem decreases {parent child : State (Source := Source)}
    (h : Step parent child) :
    GenRank.Lt (rank child) (rank parent) := by
  cases h with
  | financedBirth parent child source hused hfresh =>
      apply Or.inl
      change
        Fintype.card Source - child.usedSources.card <
          Fintype.card Source - parent.usedSources.card
      rw [hused]
      have hinsert :
          (insert source parent.usedSources).card =
            parent.usedSources.card + 1 := by
        simp [hfresh]
      rw [hinsert]
      have hcard : parent.usedSources.card < Fintype.card Source :=
        usedSources_card_lt parent hfresh
      omega
  | sourceMerge parent child hused hactive =>
      exact Or.inr ⟨by simp [rank, hused], Or.inl hactive⟩
  | cleanup parent child hused hactive =>
      exact Or.inr ⟨by simp [rank, hused], Or.inl hactive⟩
  | macroInternal parent child hused hactive hcleanup =>
      exact Or.inr ⟨by simp [rank, hused], Or.inr ⟨hactive, hcleanup⟩⟩

/-- No infinite execution can satisfy the concrete source-budget transition
rules. -/
theorem noInfinitePath :
    ¬ ∃ f : Nat → State (Source := Source),
      ∀ n, Step (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact noInfiniteDescending GenRank.wellFounded
    (fun n => rank (f n))
    (fun n => decreases (hf n))

end Step

end

end CausalBudgetCompiler
end Experimental
end PCRLean
