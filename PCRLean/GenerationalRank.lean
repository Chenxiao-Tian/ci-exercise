import Std.Tactic

namespace PCRLean

/-- The three-level rank used by the certified finite-source generation model. -/
structure GenRank where
  unusedCarrier : Nat
  activeIdentities : Nat
  cleanupHeight : Nat
  deriving Repr, DecidableEq

/-- Strict lexicographic order on the three coordinates. -/
def GenRank.Lt (x y : GenRank) : Prop :=
  x.unusedCarrier < y.unusedCarrier ∨
    (x.unusedCarrier = y.unusedCarrier ∧
      (x.activeIdentities < y.activeIdentities ∨
        (x.activeIdentities = y.activeIdentities ∧
          x.cleanupHeight < y.cleanupHeight)))

/-- Accessibility of every finite generation rank. -/
theorem GenRank.acc (r : GenRank) : Acc GenRank.Lt r := by
  rcases r with ⟨u, a, b⟩
  induction u using Nat.strongRecOn generalizing a b with
  | ind u ihu =>
      induction a using Nat.strongRecOn generalizing b with
      | ind a iha =>
          induction b using Nat.strongRecOn with
          | ind b ihb =>
              constructor
              intro r' hr
              rcases r' with ⟨u', a', b'⟩
              rcases hr with hu | ⟨hu, ha | ⟨ha, hb⟩⟩
              · exact ihu u' hu a' b'
              · subst u'
                exact iha a' ha b'
              · subst u'
                subst a'
                exact ihb b' hb

/-- The generation rank is well founded. -/
theorem GenRank.wellFounded : WellFounded GenRank.Lt :=
  ⟨GenRank.acc⟩

/-- Minimal abstract state of the finite-source certified generation chamber. -/
structure GenState where
  rank : GenRank
  deriving Repr, DecidableEq

/-- Accepted generation moves. Gauge changes and chart relabellings are not moves. -/
inductive GenStep : GenState → GenState → Prop
  | financedBirth (s t : GenState)
      (h : t.rank.unusedCarrier < s.rank.unusedCarrier) : GenStep s t
  | sourceMerge (s t : GenState)
      (hu : t.rank.unusedCarrier = s.rank.unusedCarrier)
      (ha : t.rank.activeIdentities < s.rank.activeIdentities) : GenStep s t
  | cleanup (s t : GenState)
      (hu : t.rank.unusedCarrier = s.rank.unusedCarrier)
      (ha : t.rank.activeIdentities < s.rank.activeIdentities) : GenStep s t
  | macroInternal (s t : GenState)
      (hu : t.rank.unusedCarrier = s.rank.unusedCarrier)
      (ha : t.rank.activeIdentities = s.rank.activeIdentities)
      (hb : t.rank.cleanupHeight < s.rank.cleanupHeight) : GenStep s t

/-- Every accepted generation move strictly lowers the lexicographic rank. -/
theorem GenStep.decreases {s t : GenState} (h : GenStep s t) :
    GenRank.Lt t.rank s.rank := by
  cases h with
  | financedBirth h =>
      exact Or.inl h
  | sourceMerge hu ha =>
      exact Or.inr ⟨hu, Or.inl ha⟩
  | cleanup hu ha =>
      exact Or.inr ⟨hu, Or.inl ha⟩
  | macroInternal hu ha hb =>
      exact Or.inr ⟨hu, Or.inr ⟨ha, hb⟩⟩

/-- A generic well-founded relation admits no infinite strictly descending stream. -/
theorem noInfiniteDescending {α : Sort _} {r : α → α → Prop}
    (wf : WellFounded r) (f : Nat → α)
    (hstep : ∀ n, r (f (n + 1)) (f n)) : False := by
  let P : α → Prop := fun x =>
    ∀ g : Nat → α, g 0 = x → (∀ n, r (g (n + 1)) (g n)) → False
  have hP : ∀ x, P x := by
    intro x
    induction x using wf.induction with
    | h x ih =>
        intro g hg0 hg
        let g' : Nat → α := fun n => g (n + 1)
        have hrel : r (g' 0) x := by
          simpa [g', hg0] using hg 0
        apply ih (g' 0) hrel g'
        · rfl
        · intro n
          simpa [g', Nat.add_assoc] using hg (n + 1)
  exact hP (f 0) f rfl hstep

/-- There is no infinite accepted path in the certified generation model. -/
theorem GenStep.noInfinitePath :
    ¬ ∃ f : Nat → GenState, ∀ n, GenStep (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact noInfiniteDescending GenRank.wellFounded (fun n => (f n).rank)
    (fun n => GenStep.decreases (hf n))

end PCRLean
