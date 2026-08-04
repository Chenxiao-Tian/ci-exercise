import Mathlib
import Mathlib.Data.Prod.Lex

/-!
# Exceptional interchange rank

The X038 candidate recursion orders the support dimension of the exceptional
purification--grading defect before its Artin--Rees/torsion exponent, the finite
projective-tail profile, passive complexity, contact, and exceptional debt.
A drop in an earlier coordinate remains strict even if all later coordinates
grow.

This file proves only the well-founded arithmetic.  It does not construct any
geometric coordinate or prove that an actual blowup macro lowers one.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalInterchangeRank

noncomputable section

/-- Defect support, torsion/Artin--Rees exponent, projective-tail complexity,
passive complexity, contact, and debt. -/
abbrev Rank :=
  ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))))

/-- Build the six-coordinate rank. -/
def rank
    (supportDim torsionExponent tailComplexity passive contact debt : ℕ) :
    Rank :=
  toLex (supportDim,
    toLex (torsionExponent,
      toLex (tailComplexity,
        toLex (passive,
          toLex (contact, debt)))))

/-- A support-dimension drop dominates all later coordinates. -/
theorem support_drop
    {oldSupport newSupport oldExponent newExponent oldTail newTail
      oldPassive newPassive oldContact newContact oldDebt newDebt : ℕ}
    (h : newSupport < oldSupport) :
    rank newSupport newExponent newTail newPassive newContact newDebt <
      rank oldSupport oldExponent oldTail oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- At fixed support, a torsion/Artin--Rees exponent drop is strict. -/
theorem exponent_drop
    {support oldExponent newExponent oldTail newTail oldPassive newPassive
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newExponent < oldExponent) :
    rank support newExponent newTail newPassive newContact newDebt <
      rank support oldExponent oldTail oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)

/-- At fixed support and exponent, projective-tail improvement is strict. -/
theorem tail_drop
    {support exponent oldTail newTail oldPassive newPassive
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newTail < oldTail) :
    rank support exponent newTail newPassive newContact newDebt <
      rank support exponent oldTail oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)

/-- At fixed earlier data, passive improvement dominates contact and debt. -/
theorem passive_drop
    {support exponent tail oldPassive newPassive
      oldContact newContact oldDebt newDebt : ℕ}
    (h : newPassive < oldPassive) :
    rank support exponent tail newPassive newContact newDebt <
      rank support exponent tail oldPassive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)⟩)

/-- At fixed earlier data, contact improvement dominates debt. -/
theorem contact_drop
    {support exponent tail passive oldContact newContact oldDebt newDebt : ℕ}
    (h : newContact < oldContact) :
    rank support exponent tail passive newContact newDebt <
      rank support exponent tail passive oldContact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl,
              Prod.Lex.toLex_lt_toLex.mpr
                (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)⟩)⟩)⟩)⟩)

/-- At fixed earlier data, ordinary debt cleanup is strict. -/
theorem debt_drop
    {support exponent tail passive contact oldDebt newDebt : ℕ}
    (h : newDebt < oldDebt) :
    rank support exponent tail passive contact newDebt <
      rank support exponent tail passive contact oldDebt := by
  exact Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨rfl,
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨rfl,
              Prod.Lex.toLex_lt_toLex.mpr
                (Or.inr ⟨rfl,
                  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)⟩)⟩)⟩)

/-- The complete order is well founded. -/
theorem rank_wellFounded :
    WellFounded ((· < ·) : Rank → Rank → Prop) :=
  wellFounded_lt

end

end ExceptionalInterchangeRank
end Experimental
end PCRLean
