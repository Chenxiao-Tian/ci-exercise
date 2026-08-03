import Mathlib
import PCRLean.FiniteWeightedMarkedClosure
import PCRLean.MarkedIdeal

/-!
# Centre-equivalence of finite weighted closure

The finite weighted closure is not merely permissible whenever the seed is.
It is equivalent to the original marked ideal for centre selection.  Indeed,
the empty word enrolls the source ideal at its original mark, while the
weighted power estimates show that every other residual level is automatically
permissible for every centre permissible for the source.

Thus replacing a marked ideal by its complete finite weighted packet neither
loses nor creates an allowed centre.  This is the precise no-cheating statement
needed before Hasse coefficients can be used for centre construction.
-/

namespace PCRLean
namespace WeightedMarkedEquivalence

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- Every residual level of a weighted closure is permissible for `C`. -/
def ClosurePermissible
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) (b : Nat) (C : Ideal R) : Prop :=
  ∀ m : Nat,
    FiniteWeightedMarkedClosure.levelIdeal ops I b m ≤ C ^ m

/-- A permissible source marked ideal makes the full closure permissible. -/
theorem closurePermissible_of_source
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) (b : Nat) (C : Ideal R)
    (hsource : I ≤ C ^ b) :
    ClosurePermissible ops I b C :=
  FiniteWeightedMarkedClosure.all_levels_permissible
    ops I C b hsource

/-- Closure permissibility recovers source permissibility from the empty-word
level. -/
theorem source_of_closurePermissible
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) (b : Nat) (C : Ideal R)
    (hclosure : ClosurePermissible ops I b C) :
    I ≤ C ^ b :=
  (FiniteWeightedMarkedClosure.source_le_topLevel ops I b).trans
    (hclosure b)

/-- Exact centre-equivalence of the original marked ideal and its complete
finite weighted closure. -/
theorem source_iff_closurePermissible
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) (b : Nat) (C : Ideal R) :
    I ≤ C ^ b ↔ ClosurePermissible ops I b C :=
  ⟨closurePermissible_of_source ops I b C,
    source_of_closurePermissible ops I b C⟩

/-- Marked-ideal formulation of the equivalence. -/
theorem markedPermissible_iff_closurePermissible
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) {b : Nat} (hb : 0 < b) (C : Ideal R) :
    MarkedIdeal.Permissible (R := R) ⟨I, b, hb⟩ C ↔
      ClosurePermissible ops I b C :=
  source_iff_closurePermissible ops I b C

/-- It is enough to check residual levels at most the source mark. -/
theorem closurePermissible_iff_bounded
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I : Ideal R) (b : Nat) (C : Ideal R) :
    ClosurePermissible ops I b C ↔
      ∀ m ≤ b,
        FiniteWeightedMarkedClosure.levelIdeal ops I b m ≤ C ^ m := by
  constructor
  · intro h m hm
    exact h m
  · intro h m
    by_cases hm : m ≤ b
    · exact h m hm
    · have hbot := FiniteWeightedMarkedClosure.levelIdeal_eq_bot_of_mark_lt
        ops I (Nat.lt_of_not_ge hm)
      rw [hbot]
      exact bot_le

/-- Two seed ideals with the same finite weighted levels have exactly the same
permissible centres. -/
theorem permissible_congr_of_level_eq
    (ops : κ → WeightedOperatorLedger.Operator (R := R))
    (I J : Ideal R) (b : Nat)
    (hlevels : ∀ m,
      FiniteWeightedMarkedClosure.levelIdeal ops I b m =
        FiniteWeightedMarkedClosure.levelIdeal ops J b m)
    (C : Ideal R) :
    I ≤ C ^ b ↔ J ≤ C ^ b := by
  rw [source_iff_closurePermissible ops I b C,
    source_iff_closurePermissible ops J b C]
  unfold ClosurePermissible
  constructor <;> intro h m
  · rw [← hlevels m]
    exact h m
  · rw [hlevels m]
    exact h m

end

end WeightedMarkedEquivalence
end PCRLean
