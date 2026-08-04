import Mathlib
import PCRLean.Experimental.CanonicalLayerScheduler

/-!
# Typed interface for symmetry-safe wonderful serialization

The geometric theorem suggested by the X033 round is simple once all
intersection strata are good: take the maximal building set consisting of all
nonempty intersections, blow the minimal strata first, and at each stage blow
the disjoint union of the current minimal layer.  The layer is canonical and
is preserved by every symmetry of the arrangement.

This file records the exact certificate boundary.  Lean verifies the finite
scheduler and the logical composition of the gates; it does not manufacture
regularity, passive safety, SNC compatibility, or the blow-up transform laws.
Those remain geometric theorem obligations.
-/

namespace PCRLean
namespace Experimental
namespace WonderfulLayerSerialization

noncomputable section

universe u

open CanonicalLayerScheduler

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- All geometric conditions required of one simultaneous layer centre. -/
structure LayerGate (F : RankedFamily (α := α)) (k : ℕ) : Prop where
  transformed_pairwise_disjoint : Prop
  regular_disjoint_union : Prop
  active_owner_legal : Prop
  passive_owner_safe : Prop
  boundary_snc_compatible : Prop
  nonidentity_action : Prop

namespace LayerGate

variable {F : RankedFamily (α := α)} {k : ℕ}

/-- Conjunction form used by downstream compilers. -/
def Holds (G : LayerGate F k) : Prop :=
  G.transformed_pairwise_disjoint ∧
  G.regular_disjoint_union ∧
  G.active_owner_legal ∧
  G.passive_owner_safe ∧
  G.boundary_snc_compatible ∧
  G.nonidentity_action

/-- Every typed layer gate exposes its complete conjunction. -/
theorem holds (G : LayerGate F k) : G.Holds := by
  exact ⟨G.transformed_pairwise_disjoint,
    G.regular_disjoint_union,
    G.active_owner_legal,
    G.passive_owner_safe,
    G.boundary_snc_compatible,
    G.nonidentity_action⟩

end LayerGate

/-- A finite ordinary-centre word certificate produced from the canonical
rank-layer schedule. -/
structure WordCertificate (F : RankedFamily (α := α)) : Prop where
  schedule : List (Finset α)
  schedule_eq : schedule = F.schedule
  gate : ∀ k, k ≤ F.maxRank → LayerGate F k
  all_gates_hold : ∀ k, k ≤ F.maxRank → (gate k ‹_›).Holds
  length_eq : schedule.length = F.maxRank + 1

/-- Compile a word certificate from one geometric gate for every bounded
layer.  This is the exact handoff from geometry to the finite scheduler. -/
def compile
    (F : RankedFamily (α := α))
    (gate : ∀ k, k ≤ F.maxRank → LayerGate F k) :
    WordCertificate F where
  schedule := F.schedule
  schedule_eq := rfl
  gate := gate
  all_gates_hold := by
    intro k hk
    exact (gate k hk).holds
  length_eq := F.schedule_length

/-- The compiled word is finite with the explicit sharp formal bound. -/
theorem compiled_length
    (F : RankedFamily (α := α))
    (gate : ∀ k, k ≤ F.maxRank → LayerGate F k) :
    (compile F gate).schedule.length = F.maxRank + 1 :=
  (compile F gate).length_eq

/-- Rank-preserving symmetries fix the underlying canonical schedule. -/
theorem schedule_equivariant
    (F : RankedFamily (α := α))
    (e : α ≃ α)
    (hrank : ∀ a, F.rank (e a) = F.rank a) :
    F.schedule.map (fun s => s.map e.toEmbedding) = F.schedule :=
  F.map_schedule_eq e hrank

/-- The exact remaining geometric burden for a clean maximal-building-set
chamber.  The fields are intentionally explicit and may not be replaced by a
single opaque `legal` Boolean. -/
structure CleanBuildingSetGeometry
    (F : RankedFamily (α := α)) : Prop where
  intersection_strata_regular : Prop
  minimal_layer_transforms_disjoint :
    ∀ k, k ≤ F.maxRank → Prop
  regular_layer_union :
    ∀ k, k ≤ F.maxRank → Prop
  active_legality :
    ∀ k, k ≤ F.maxRank → Prop
  passive_safety :
    ∀ k, k ≤ F.maxRank → Prop
  boundary_compatibility :
    ∀ k, k ≤ F.maxRank → Prop
  nonidentity :
    ∀ k, k ≤ F.maxRank → Prop

/-- Clean geometry supplies the scheduler's layer gates. -/
def CleanBuildingSetGeometry.toGates
    {F : RankedFamily (α := α)}
    (G : CleanBuildingSetGeometry F) :
    ∀ k, k ≤ F.maxRank → LayerGate F k := by
  intro k hk
  exact
    { transformed_pairwise_disjoint :=
        G.minimal_layer_transforms_disjoint k hk
      regular_disjoint_union := G.regular_layer_union k hk
      active_owner_legal := G.active_legality k hk
      passive_owner_safe := G.passive_safety k hk
      boundary_snc_compatible := G.boundary_compatibility k hk
      nonidentity_action := G.nonidentity k hk }

/-- Conditional clean-chamber compiler. -/
def compileClean
    (F : RankedFamily (α := α))
    (G : CleanBuildingSetGeometry F) :
    WordCertificate F :=
  compile F G.toGates

end

end WonderfulLayerSerialization
end Experimental
end PCRLean
