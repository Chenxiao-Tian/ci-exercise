import Mathlib

/-!
# Fractal proof engine: architecture-only closure theorem

This file contains no missing mathematical bridge. It formalizes the generic
logic of a finite typed proof graph: every node has a finite predecessor set,
every predecessor has smaller rank, and an `EdgePackage` supplies a proof that
predecessor claims imply the parent claim. The closure theorem derives any
designated root claim.

Concrete positive-characteristic-resolution claims and semantic edge
certificates must be supplied by separate kernel-checked declarations. This
file is not a proof of resolution and is not imported into `CertifiedIndex`.
-/

namespace PCRLean
namespace Blueprint
namespace FractalProofEngine

universe u

structure Architecture where
  Node : Type u
  [nodeFintype : Fintype Node]
  [nodeDecidableEq : DecidableEq Node]
  deps : Node → Finset Node
  rank : Node → Nat
  dep_rank_lt : ∀ {parent child}, child ∈ deps parent → rank child < rank parent

attribute [instance] Architecture.nodeFintype Architecture.nodeDecidableEq

namespace Architecture

variable (A : Architecture)

/-- Dependency relation: `child` is required to prove `parent`. -/
def DepRel (child parent : A.Node) : Prop := child ∈ A.deps parent

/-- The declared dependency graph is well founded when every edge lowers rank. -/
theorem depRel_wellFounded : WellFounded A.DepRel := by
  apply WellFounded.intro
  intro n
  induction h : A.rank n using Nat.strong_induction_on generalizing n with
  | h k ih =>
      constructor
      intro d hd
      exact ih (A.rank d) (A.dep_rank_lt hd) d rfl

end Architecture

/-- Mathematical meanings assigned to graph nodes. -/
structure Semantics (A : Architecture) where
  claim : A.Node → Prop

/-- A certified semantic edge for every graph node. -/
structure EdgePackage (A : Architecture) (S : Semantics A) where
  compose : ∀ n : A.Node,
    (∀ d, d ∈ A.deps n → S.claim d) → S.claim n

/-- Close every node by well-founded recursion through certified edges. -/
noncomputable def closeAll
    (A : Architecture) (S : Semantics A) (E : EdgePackage A S) :
    ∀ n : A.Node, S.claim n :=
  A.depRel_wellFounded.fix fun n ih =>
    E.compose n fun d hd => ih d hd

/-- Any designated root follows once all semantic edge certificates exist. -/
theorem root_of_edgePackage
    (A : Architecture) (S : Semantics A) (E : EdgePackage A S)
    (root : A.Node) : S.claim root :=
  closeAll A S E root

/-- First-class refinement certificate for a parent from a finite child family. -/
structure Refinement
    {Node : Type u} (Claim : Node → Prop) (parent : Node)
    (children : Finset Node) where
  sound : (∀ child, child ∈ children → Claim child) → Claim parent

end FractalProofEngine
end Blueprint
end PCRLean