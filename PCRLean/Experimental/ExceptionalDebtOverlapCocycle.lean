import PCRLean.Experimental.ExceptionalDebtOverlapTransport

/-!
# Cocycle composition for exceptional debt overlaps

Two overlap transitions compose to a third one.  If

`E₁ ↦ u₁₂ E₂` and `E₂ ↦ u₂₃ E₃`,

then the composite sends

`E₁ ↦ (φ₂₃(u₁₂) u₂₃) E₃`,

and the composite coefficient is again a unit.  Consequently exceptional debt
transport is transitive and satisfies the algebraic cocycle law forced by ring
equivalence composition.

This does not construct the geometric overlap maps.  It proves that once the
unit transition data are supplied, no chart path can change the debt ideal or
its exponent.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalDebtOverlapCocycle

noncomputable section

universe u v w x

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]

open ExceptionalDebtOverlapTransport

/-- Composite overlap transition. -/
noncomputable def trans
    (O₁₂ : Overlap (A := A) (B := B))
    (O₂₃ : Overlap (A := B) (B := C))
    (hmiddle : O₁₂.rightExceptional = O₂₃.leftExceptional) :
    Overlap (A := A) (B := C) where
  equiv := O₁₂.equiv.trans O₂₃.equiv
  leftExceptional := O₁₂.leftExceptional
  rightExceptional := O₂₃.rightExceptional
  unit := O₂₃.equiv O₁₂.unit * O₂₃.unit
  unit_isUnit := by
    exact (O₁₂.unit_isUnit.map O₂₃.equiv.toMonoidHom).mul O₂₃.unit_isUnit
  exceptional_eq := by
    change O₂₃.equiv (O₁₂.equiv O₁₂.leftExceptional) =
      (O₂₃.equiv O₁₂.unit * O₂₃.unit) * O₂₃.rightExceptional
    rw [O₁₂.exceptional_eq, map_mul, hmiddle, O₂₃.exceptional_eq]
    ac_rfl

/-- Debt transport through the composite overlap. -/
theorem map_debtIdeal_trans
    (O₁₂ : Overlap (A := A) (B := B))
    (O₂₃ : Overlap (A := B) (B := C))
    (hmiddle : O₁₂.rightExceptional = O₂₃.leftExceptional)
    (δ : Nat) :
    Ideal.map (trans O₁₂ O₂₃ hmiddle).equiv
        (debtIdeal O₁₂.leftExceptional δ) =
      debtIdeal O₂₃.rightExceptional δ :=
  (trans O₁₂ O₂₃ hmiddle).map_debtIdeal δ

section Lineage

variable {Source : Type x} [DecidableEq Source]
variable {E : ExceptionalDebtLineage.Event (Source := Source)}

/-- Event debt is independent of a two-overlap path. -/
theorem map_eventDebt_trans
    (O₁₂ : EventOverlap (A := A) (B := B) E)
    (O₂₃ : EventOverlap (A := B) (B := C) E)
    (hmiddle : O₁₂.toOverlap.rightExceptional =
      O₂₃.toOverlap.leftExceptional) :
    Ideal.map (trans O₁₂.toOverlap O₂₃.toOverlap hmiddle).equiv
        (debtIdeal O₁₂.toOverlap.leftExceptional E.debt) =
      debtIdeal O₂₃.toOverlap.rightExceptional E.debt :=
  map_debtIdeal_trans O₁₂.toOverlap O₂₃.toOverlap hmiddle E.debt

end Lineage

end

end ExceptionalDebtOverlapCocycle
end Experimental
end PCRLean
