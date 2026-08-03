import Mathlib
import PCRLean.Experimental.ExceptionalDebtLedger
import PCRLean.Experimental.PolynomialGraphMarkedTransformDebt

/-!
# Global debt identities for polynomial graph charts

For `0 < mark ≤ q`, the positive mark determines one element of `Fin q` and
hence one global debt key `(ancestorSource, mark)`.  The key is independent of
the standard blowup chart.

The graph-chart residual ideal is exactly the exceptional pivot ideal raised to
the exponent stored in this key.  Thus all pivot charts are local occurrences
of the same debt event.  Registering each chart separately would be source
cloning and is explicitly excluded by the data model.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphDebtIdentity

noncomputable section

universe u v w

variable {Source : Type u} {Chart : Type v}
variable {R : Type w} [CommRing R] [IsDomain R]
variable {ι : Type*} [DecidableEq ι]

open ExceptionalDebtLedger
open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt

/-- Finite mark index represented by a positive mark below the block. -/
def markIndex
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) : Fin q :=
  ⟨mark - 1, by omega⟩

/-- The mark index recovers the original positive mark. -/
theorem markIndex_actualMark
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    actualMark (Source := Source)
      (Classical.arbitrary Source, markIndex q mark hmark_pos hmark_le) = mark := by
  simp [actualMark, markIndex]
  omega

/-- Global debt key attached to one ancestor source. -/
def debtKey
    (source : Source)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    DebtKey Source q :=
  (source, markIndex q mark hmark_pos hmark_le)

/-- The key stores exactly the original mark. -/
theorem debtKey_actualMark
    (source : Source)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    actualMark (debtKey source q mark hmark_pos hmark_le) = mark := by
  simp [actualMark, debtKey, markIndex]
  omega

/-- The key stores exactly the graph exceptional-debt exponent. -/
theorem debtKey_exponent
    (source : Source)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    exponent (debtKey source q mark hmark_pos hmark_le) = q - mark := by
  rw [exponent, debtKey_actualMark]

/-- One chart-local occurrence of the global graph debt. -/
def occurrence
    (source : Source) (chart : Chart)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    Occurrence Source Chart q where
  key := debtKey source q mark hmark_pos hmark_le
  chart := chart

/-- Any two chart occurrences constructed from the same ancestor and mark have
the same global event key. -/
theorem occurrence_key_independent_of_chart
    (source : Source) (c d : Chart)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    (occurrence source c q mark hmark_pos hmark_le).key =
      (occurrence source d q mark hmark_pos hmark_le).key := rfl

/-- The graph residual ideal is the exceptional power recorded by the global
debt key. -/
theorem graphResidualIdeal_eq_keyExponent
    (source : Source)
    (k : ι)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    transformedMarkedRootIdeal (R := R) k q mark =
      (pivotIdeal (R := R) k) ^
        exponent (debtKey source q mark hmark_pos hmark_le) := by
  rw [debtKey_exponent]
  exact transformedMarkedRootIdeal_eq_pivotPower
    (R := R) k q mark

/-- Chart transport preserves both the event key and its exceptional exponent. -/
theorem occurrence_exponent_independent_of_chart
    (source : Source) (c d : Chart)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark_le : mark ≤ q) :
    exponent (occurrence source c q mark hmark_pos hmark_le).key =
      exponent (occurrence source d q mark hmark_pos hmark_le).key := rfl

end

end PolynomialGraphDebtIdentity
end Experimental
end PCRLean
