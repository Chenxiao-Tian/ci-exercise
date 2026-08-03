import Mathlib

/-!
# Well-founded rank for Frobenius digit recursion

A Frobenius digit expansion has two kinds of recursive children.

* The zero digit remains at the same marked order but moves to a lower
  Frobenius level.
* Every positive digit remains at the same Frobenius level but has strictly
  smaller residual marked order.

Lexicographic order on `(Frobenius level, marked order)` is therefore
well-founded.  Its finite-multiset extension controls branching into all digits
simultaneously.
-/

namespace PCRLean
namespace FrobeniusDigitRank

noncomputable section

/-- Frobenius depth followed by residual marked order. -/
structure Rank where
  depth : Nat
  mark : Nat
  deriving DecidableEq, Repr

/-- Lexicographic strict order. -/
def Lt (a b : Rank) : Prop :=
  a.depth < b.depth ∨
    (a.depth = b.depth ∧ a.mark < b.mark)

instance : LT Rank := ⟨Lt⟩

/-- Embedding into the standard lexicographic product. -/
def toProd (r : Rank) : Nat × Nat := (r.depth, r.mark)

/-- The rank relation is exactly product lexicographic order. -/
theorem lt_iff_prodLex (a b : Rank) :
    a < b ↔ Prod.Lex (· < ·) (· < ·) a.toProd b.toProd := by
  rfl

/-- Well-foundedness of Frobenius digit rank. -/
theorem wellFounded : WellFounded ((· < ·) : Rank → Rank → Prop) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s hs
  let depths : Set Nat := {d | ∃ r ∈ s, r.depth = d}
  have hdepths : depths.Nonempty := by
    rcases hs with ⟨r, hr⟩
    exact ⟨r.depth, r, hr, rfl⟩
  let d := sInf depths
  have hdmem : d ∈ depths := Nat.sInf_mem hdepths
  let marks : Set Nat := {m | ∃ r ∈ s, r.depth = d ∧ r.mark = m}
  have hmarks : marks.Nonempty := by
    rcases hdmem with ⟨r, hr, hrd⟩
    exact ⟨r.mark, r, hr, hrd, rfl⟩
  let m := sInf marks
  have hmmem : m ∈ marks := Nat.sInf_mem hmarks
  rcases hmmem with ⟨r, hr, hrd, hrm⟩
  refine ⟨r, hr, ?_⟩
  intro y hy hyr
  rcases hyr with hdepth | ⟨hdepth, hmark⟩
  · have hyd : y.depth ∈ depths := ⟨y, hy, rfl⟩
    have hdle : d ≤ y.depth := Nat.sInf_le hyd
    rw [hrd] at hdepth
    omega
  · have hym : y.mark ∈ marks := ⟨y, hy, hdepth, rfl⟩
    have hmle : m ≤ y.mark := Nat.sInf_le hym
    rw [hrm] at hmark
    omega

/-- The zero digit strictly lowers rank by lowering Frobenius depth. -/
theorem zeroDigit_decreases
    {depth mark : Nat} (hdepth : 0 < depth) :
    Rank.mk (depth - 1) mark < Rank.mk depth mark := by
  left
  omega

/-- Every positive digit with smaller residual mark strictly lowers rank. -/
theorem positiveDigit_decreases
    {depth childMark parentMark : Nat}
    (hmark : childMark < parentMark) :
    Rank.mk depth childMark < Rank.mk depth parentMark := by
  exact Or.inr ⟨rfl, hmark⟩

/-- A child obtained by consuming a positive operator cost has smaller marked
rank whenever that cost is visible. -/
theorem costDigit_decreases
    {depth mark cost : Nat} (hcost : 0 < cost) (hle : cost ≤ mark) :
    Rank.mk depth (mark - cost) < Rank.mk depth mark := by
  apply positiveDigit_decreases
  omega

/-- There is no infinite branch of strictly decreasing Frobenius digit ranks. -/
theorem no_infinite_branch :
    ¬ ∃ f : Nat → Rank, ∀ n, f (n + 1) < f n := by
  intro h
  rcases h with ⟨f, hf⟩
  exact WellFounded.not_descending_chain wellFounded f hf

/-- The finite multiset extension used for a branching digit packet. -/
abbrev MultisetLt : Multiset Rank → Multiset Rank → Prop :=
  Multiset.IsDershowitzMannaLT ((· < ·) : Rank → Rank → Prop)

/-- Branching into finitely many lower-rank digits is also well-founded. -/
theorem multisetWellFounded : WellFounded MultisetLt :=
  Multiset.wellFounded_isDershowitzMannaLT wellFounded

end

end FrobeniusDigitRank
end PCRLean
