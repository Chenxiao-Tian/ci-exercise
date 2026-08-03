import Mathlib

/-!
# Final proof blueprint: architecture-only dependency verification

This file does **not** assert any unproved mathematical bridge. It encodes the
65 load-bearing groups of `MLEL-D001 / FCPP-ATLAS` as an acyclic dependency
graph. A `ProofPackage` supplies a proof of each node from proofs of its listed
dependencies. The final theorem shows that such a package yields the final
resolution claim. Thus Lean checks the engineering topology and detects a
missing or cyclic dependency, while the mathematical contents of the nodes
remain independent obligations.
-/

namespace PCRLean
namespace Blueprint
namespace FinalProofAtlas

inductive Node where
  | g01 | g02 | g03 | g04 | g05 | g06 | g07 | g08 | g09 | g10
  | g11 | g12 | g13 | g14 | g15 | g16 | g17 | g18 | g19 | g20
  | g21 | g22 | g23 | g24 | g25 | g26 | g27 | g28 | g29 | g30
  | g31 | g32 | g33 | g34 | g35 | g36 | g37 | g38 | g39 | g40
  | g41 | g42 | g43 | g44 | g45 | g46 | g47 | g48 | g49 | g50
  | g51 | g52 | g53 | g54 | g55 | g56 | g57 | g58 | g59 | g60
  | g61 | g62 | g63 | g64 | g65
deriving DecidableEq, Repr, Fintype

def rank : Node → Nat
  | .g01 => 0 | .g02 => 1 | .g03 => 2 | .g04 => 3 | .g05 => 4
  | .g06 => 5 | .g07 => 6 | .g08 => 7 | .g09 => 8 | .g10 => 9
  | .g11 => 10 | .g12 => 11 | .g13 => 12 | .g14 => 13 | .g15 => 14
  | .g16 => 15 | .g17 => 16 | .g18 => 17 | .g19 => 18 | .g20 => 19
  | .g21 => 20 | .g22 => 21 | .g23 => 22 | .g24 => 23 | .g25 => 24
  | .g26 => 25 | .g27 => 26 | .g28 => 27 | .g29 => 28 | .g30 => 29
  | .g31 => 30 | .g32 => 31 | .g33 => 32 | .g34 => 33 | .g35 => 34
  | .g36 => 35 | .g37 => 36 | .g38 => 37 | .g39 => 38 | .g40 => 39
  | .g41 => 40 | .g42 => 41 | .g43 => 42 | .g44 => 43 | .g45 => 44
  | .g46 => 45 | .g47 => 46 | .g48 => 47 | .g49 => 48 | .g50 => 49
  | .g51 => 50 | .g52 => 51 | .g53 => 52 | .g54 => 53 | .g55 => 54
  | .g56 => 55 | .g57 => 56 | .g58 => 57 | .g59 => 58 | .g60 => 59
  | .g61 => 60 | .g62 => 61 | .g63 => 62 | .g64 => 63 | .g65 => 64

def deps : Node → List Node
  | .g01 => []
  | .g02 => [.g01]
  | .g03 => [.g02]
  | .g04 => [.g02]
  | .g05 => [.g04]
  | .g06 => [.g04]
  | .g07 => [.g03, .g06]
  | .g08 => [.g07]
  | .g09 => [.g08]
  | .g10 => [.g09]
  | .g11 => [.g09]
  | .g12 => [.g03, .g04]
  | .g13 => [.g03, .g08]
  | .g14 => [.g10, .g11, .g12, .g13]
  | .g15 => [.g10, .g14]
  | .g16 => [.g11, .g14]
  | .g17 => [.g12, .g16]
  | .g18 => [.g05, .g11, .g14]
  | .g19 => [.g12, .g18]
  | .g20 => [.g14, .g18]
  | .g21 => [.g15, .g16, .g19, .g20]
  | .g22 => [.g13, .g21]
  | .g23 => [.g05, .g21]
  | .g24 => [.g21, .g22, .g23]
  | .g25 => [.g14, .g18, .g19, .g20, .g24]
  | .g26 => [.g15, .g16, .g17, .g18, .g19, .g20, .g21, .g22, .g23, .g24, .g25]
  | .g27 => [.g26]
  | .g28 => [.g26]
  | .g29 => [.g22, .g28]
  | .g30 => [.g22, .g26]
  | .g31 => [.g27, .g28, .g29, .g30]
  | .g32 => [.g31]
  | .g33 => [.g32]
  | .g34 => [.g12, .g33]
  | .g35 => [.g33, .g34]
  | .g36 => [.g03, .g34]
  | .g37 => [.g04, .g35, .g36]
  | .g38 => [.g03, .g35, .g36]
  | .g39 => [.g07, .g35, .g37, .g38]
  | .g40 => [.g31, .g34, .g39]
  | .g41 => [.g31, .g32, .g33, .g34, .g35, .g36, .g37, .g38, .g39, .g40]
  | .g42 => [.g40]
  | .g43 => [.g41, .g42]
  | .g44 => [.g34, .g40, .g42]
  | .g45 => [.g11, .g16, .g41]
  | .g46 => [.g18, .g41]
  | .g47 => [.g41, .g43, .g44]
  | .g48 => [.g25, .g47]
  | .g49 => [.g41]
  | .g50 => [.g49]
  | .g51 => [.g41, .g49, .g50]
  | .g52 => [.g43, .g44, .g45, .g46, .g47, .g48, .g51]
  | .g53 => [.g26, .g41, .g52]
  | .g54 => [.g21, .g35, .g41]
  | .g55 => [.g22, .g54]
  | .g56 => [.g25, .g48, .g54, .g55]
  | .g57 => [.g20, .g56]
  | .g58 => [.g03, .g07, .g31, .g41, .g42, .g52, .g57]
  | .g59 => [.g12, .g58]
  | .g60 => [.g53, .g54, .g55, .g56, .g57, .g58, .g59]
  | .g61 => [.g01, .g02, .g60]
  | .g62 => [.g01, .g53, .g60, .g61]
  | .g63 => [.g62]
  | .g64 => [.g17, .g24, .g31, .g37, .g38, .g43, .g47, .g51]
  | .g65 => [.g62, .g63, .g64]

theorem dep_rank_lt {n d : Node} (h : d ∈ deps n) : rank d < rank n := by
  cases n <;> simp [deps, rank] at h ⊢ <;> omega

def DepRel (d n : Node) : Prop := d ∈ deps n

theorem depRel_wellFounded : WellFounded DepRel := by
  refine Subrelation.wf (fun d n h => dep_rank_lt h) (measure_wf rank)

/-- Abstract meanings of the 65 mathematical claims. -/
structure Semantics where
  claim : Node → Prop

/-- A proof of every node from proofs of exactly its predecessors. -/
structure ProofPackage (S : Semantics) where
  prove : ∀ n : Node, (∀ d, d ∈ deps n → S.claim d) → S.claim n

noncomputable def proveNode {S : Semantics} (P : ProofPackage S) :
    ∀ n : Node, S.claim n :=
  depRel_wellFounded.fix fun n ih => P.prove n fun d hd => ih d hd

/-- Final group: proof-to-Lean alignment, whose claim includes the final resolution theorem. -/
def finalNode : Node := .g65

theorem blueprint_implies_final_claim {S : Semantics} (P : ProofPackage S) :
    S.claim finalNode :=
  proveNode P finalNode

/-- The six paper boundary nodes. -/
def paperEnds : List Node := [.g13, .g26, .g41, .g53, .g61, .g65]

theorem paperEnds_strictly_increase :
    List.Pairwise (fun a b => rank a < rank b) paperEnds := by
  simp [paperEnds, rank]

end FinalProofAtlas
end Blueprint
end PCRLean
