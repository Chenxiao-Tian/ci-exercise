import Mathlib

/-!
# Finite weighted operator packets

Differential and Hasse operators consume marked order.  This file records that
consumption explicitly.  A weighted operator of positive cost `r` is required
to send `C^n` into `C^(n-r)` for every candidate centre ideal `C`.  Iterating a
word of operators then consumes the sum of the costs.

Positive costs make the part of the operator orbit visible below a fixed mark
finite.  Thus an apparently infinite differential orbit has a finite weighted
packet at every marked level, and every member of that packet remains
permissible for any centre that was permissible for the seed.

The file is independent of coordinates.  To apply it to Hasse--Schmidt
operators one must separately prove the divided-power Leibniz estimate
`D_r(C^n) ⊆ C^(n-r)` for the geometric operator family in question.
-/

namespace PCRLean
namespace WeightedOperatorLedger

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {κ : Type v}

/-- An additive operator together with its positive marked-order cost and the
power estimate that makes it legal for marked-centre bookkeeping. -/
structure Operator where
  op : R →+ R
  cost : Nat
  cost_pos : 0 < cost
  power_safe : ∀ (C : Ideal R) (n : Nat) {x : R},
    x ∈ C ^ n → op x ∈ C ^ (n - cost)

/-- Total marked-order cost of a finite operator word. -/
def wordCost (ops : κ → Operator (R := R)) : List κ → Nat
  | [] => 0
  | i :: word => (ops i).cost + wordCost ops word

/-- Apply a finite operator word, with the head acting last on the recursively
computed tail. -/
def applyWord (ops : κ → Operator (R := R)) : List κ → R → R
  | [], x => x
  | i :: word, x => (ops i).op (applyWord ops word x)

@[simp] theorem wordCost_nil (ops : κ → Operator (R := R)) :
    wordCost ops [] = 0 := rfl

@[simp] theorem wordCost_cons (ops : κ → Operator (R := R))
    (i : κ) (word : List κ) :
    wordCost ops (i :: word) = (ops i).cost + wordCost ops word := rfl

@[simp] theorem applyWord_nil (ops : κ → Operator (R := R)) (x : R) :
    applyWord ops [] x = x := rfl

@[simp] theorem applyWord_cons (ops : κ → Operator (R := R))
    (i : κ) (word : List κ) (x : R) :
    applyWord ops (i :: word) x = (ops i).op (applyWord ops word x) := rfl

/-- The marked-power estimate survives every finite operator word. -/
theorem applyWord_mem_power
    (ops : κ → Operator (R := R))
    (C : Ideal R) {n : Nat} {x : R} (hx : x ∈ C ^ n)
    (word : List κ) :
    applyWord ops word x ∈ C ^ (n - wordCost ops word) := by
  induction word with
  | nil => simpa
  | cons i word ih =>
      have hstep := (ops i).power_safe C
        (n - wordCost ops word) ih
      simpa [Nat.sub_sub, Nat.add_comm] using hstep

/-- Positive costs dominate word length. -/
theorem length_le_wordCost
    (ops : κ → Operator (R := R)) (word : List κ) :
    word.length ≤ wordCost ops word := by
  induction word with
  | nil => simp
  | cons i word ih =>
      have hi := (ops i).cost_pos
      simp only [List.length_cons, wordCost_cons]
      omega

section FiniteAlphabet

variable [Fintype κ] [DecidableEq κ]

/-- Explicit finite set of all words of length at most `n`. -/
def wordsAtMost : Nat → Finset (List κ)
  | 0 => {[]}
  | n + 1 =>
      {[]} ∪
        ((Finset.univ.product (wordsAtMost n)).image
          (fun p : κ × List κ => p.1 :: p.2))

@[simp] theorem mem_wordsAtMost_iff (n : Nat) (word : List κ) :
    word ∈ wordsAtMost (κ := κ) n ↔ word.length ≤ n := by
  induction n generalizing word with
  | zero =>
      cases word <;> simp [wordsAtMost]
  | succ n ih =>
      cases word with
      | nil => simp [wordsAtMost]
      | cons i word =>
          simp [wordsAtMost, ih]

/-- Words whose total cost is visible below the fixed mark `b`. -/
def boundedWords (ops : κ → Operator (R := R)) (b : Nat) :
    Finset (List κ) :=
  (wordsAtMost (κ := κ) b).filter
    (fun word => wordCost ops word ≤ b)

@[simp] theorem mem_boundedWords_iff
    (ops : κ → Operator (R := R)) (b : Nat) (word : List κ) :
    word ∈ boundedWords ops b ↔ wordCost ops word ≤ b := by
  rw [boundedWords, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hcost
    exact ⟨(mem_wordsAtMost_iff b word).2
      ((length_le_wordCost ops word).trans hcost), hcost⟩

/-- Finite packet of all weighted descendants visible at mark `b`.  Each entry
stores both the descendant equation and its residual mark. -/
noncomputable def descendantPacket
    (ops : κ → Operator (R := R)) (seed : R) (b : Nat) :
    Finset (R × Nat) := by
  classical
  exact (boundedWords ops b).image
    (fun word => (applyWord ops word seed, b - wordCost ops word))

/-- Every word whose total cost is at most the mark occurs in the finite
weighted packet. -/
theorem mem_descendantPacket_of_cost_le
    (ops : κ → Operator (R := R)) (seed : R) (b : Nat)
    (word : List κ) (hcost : wordCost ops word ≤ b) :
    (applyWord ops word seed, b - wordCost ops word) ∈
      descendantPacket ops seed b := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨word, (mem_boundedWords_iff ops b word).2 hcost, rfl⟩

/-- Every element of the finite packet is represented by an operator word of
bounded total cost. -/
theorem descendantPacket_sound
    (ops : κ → Operator (R := R)) (seed : R) (b : Nat)
    {entry : R × Nat} (hentry : entry ∈ descendantPacket ops seed b) :
    ∃ word : List κ,
      wordCost ops word ≤ b ∧
      entry = (applyWord ops word seed, b - wordCost ops word) := by
  classical
  rcases Finset.mem_image.mp hentry with ⟨word, hword, rfl⟩
  exact ⟨word, (mem_boundedWords_iff ops b word).1 hword, rfl⟩

/-- If the seed lies in the marked power of a centre, every finite weighted
descendant lies in the power prescribed by its residual mark. -/
theorem descendantPacket_permissible
    (ops : κ → Operator (R := R))
    (C : Ideal R) {seed : R} {b : Nat}
    (hseed : seed ∈ C ^ b)
    {entry : R × Nat} (hentry : entry ∈ descendantPacket ops seed b) :
    entry.1 ∈ C ^ entry.2 := by
  rcases descendantPacket_sound ops seed b hentry with
    ⟨word, hcost, rfl⟩
  exact applyWord_mem_power ops C hseed word

/-- The visible weighted orbit is genuinely finite, independently of the size
of the unrestricted operator orbit. -/
theorem finite_visible_descendants
    (ops : κ → Operator (R := R)) (seed : R) (b : Nat) :
    Set.Finite
      ({entry : R × Nat | entry ∈ descendantPacket ops seed b} :
        Set (R × Nat)) := by
  classical
  simpa using (descendantPacket ops seed b).finite_toSet

end FiniteAlphabet

end

end WeightedOperatorLedger
end PCRLean
