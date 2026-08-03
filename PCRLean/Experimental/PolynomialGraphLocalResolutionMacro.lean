import Mathlib
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate
import PCRLean.Experimental.PolynomialGraphPassiveSafety
import PCRLean.Experimental.PolynomialGraphBoundaryStrata
import PCRLean.Experimental.PolynomialGraphDebtCausalReentry

/-!
# A full local resolution macro for polynomial graph Frobenius packets

This module compiles the current graph-centre research into one local macro.
The input consists of:

* a Noetherian regular coefficient domain `R` of characteristic `p`;
* a nonempty finite polynomial graph centre `Z_i-h_i`;
* a prime-power root block `q = p^e` with positive mark `m ≤ q`;
* passive data induced from an `R`-flat module;
* a finite boundary family whose every stratum quotient is regular; and
* one fixed finite ancestor-source ledger.

The output supplies, for the same actual centre:

* properness, non-whole-centre strictness, finite type and regular quotient;
* active marked permissibility;
* passive Tor safety along all centre powers and flat centre restriction;
* exact regular intersection with every boundary stratum;
* every standard blowup chart and exact controlled factorization; and
* a source-conservative causal transition.

Every chart has exactly one of two outcomes:

1. `mark = p^e`: the transformed root packet is the unit ideal; or
2. `mark < p^e`: the transformed packet is the pure exceptional debt
   `(E_k)^(p^e-mark)`, and the concrete finite-source rank strictly decreases
   without changing source support or the number of active identities.

This is an actual local resolution macro, not a general resolution theorem.
The universal proof must still extract and glue these graph models from an
arbitrary differential Rees state and handle passive data not induced from a
flat coefficient module.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphLocalResolutionMacro

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
variable {β : Type x} [Fintype β] [DecidableEq β]
variable {Source : Type y} [Fintype Source] [DecidableEq Source]
variable [IsNoetherianRing R] [IsRegularRing R]

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt

abbrev P := MvPolynomial ι R

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Full local macro certificate. -/
structure Certificate
    (h : ι → R)
    (boundary : β → Ideal R)
    (activeSources : Finset (Finset Source))
    (e mark : Nat) where
  mark_pos : 0 < mark
  mark_le_block : mark ≤ p ^ e
  centre :
    PolynomialGraphFrobeniusCentreCertificate.Certificate p h e
  active :
    PolynomialGraphArbitraryMarkCertificate.Certificate p h e mark
  passive :
    PolynomialGraphPassiveSafety.Certificate
      (R := R) (ι := ι) (N := N) h
  boundaryStrata :
    PolynomialGraphBoundaryStrata.Certificate h boundary
  causalReentry : ∀ k : ι,
    PolynomialGraphDebtCausalReentry.ReentryCertificate
      (R := R) activeSources k (p ^ e) mark
  chartResidual : ∀ k : ι,
    transformedMarkedRootIdeal (R := R) k (p ^ e) mark =
      (pivotIdeal (R := R) k) ^ (p ^ e - mark)
  chartOutcome :
    (mark = p ^ e ∧ ∀ k : ι,
      transformedMarkedRootIdeal (R := R) k (p ^ e) mark = ⊤) ∨
    (mark < p ^ e ∧ 0 < p ^ e - mark ∧
      ∀ k : ι,
        transformedMarkedRootIdeal (R := R) k (p ^ e) mark =
          (pivotIdeal (R := R) k) ^ (p ^ e - mark))
  rankDecrease :
    GenRank.Lt
      (PolynomialGraphDebtCausalReentry.childState
        activeSources (p ^ e) mark).rank
      (PolynomialGraphDebtCausalReentry.parentState
        activeSources (p ^ e)).rank

/-- Assemble the complete local macro. -/
noncomputable def certificate
    (h : ι → R)
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    Certificate (R := R) (ι := ι) (N := N)
      p h boundary activeSources e mark where
  mark_pos := hmark_pos
  mark_le_block := hmark_le
  centre :=
    PolynomialGraphFrobeniusCentreCertificate.certificate p h e
  active :=
    PolynomialGraphArbitraryMarkCertificate.certificate
      p h e mark hmark_pos hmark_le
  passive :=
    PolynomialGraphPassiveSafety.certificate
      (R := R) (ι := ι) (N := N) h
  boundaryStrata :=
    PolynomialGraphBoundaryStrata.certificate h boundary hboundary
  causalReentry := fun k =>
    PolynomialGraphDebtCausalReentry.reentryCertificate
      (R := R) activeSources k (p ^ e) mark hmark_pos hmark_le
  chartResidual := fun k =>
    transformedMarkedRootIdeal_eq_pivotPower
      (R := R) k (p ^ e) mark
  chartOutcome := by
    by_cases hexact : mark = p ^ e
    · left
      refine ⟨hexact, ?_⟩
      intro k
      subst mark
      exact transformedMarkedRootIdeal_eq_top_of_exactMark
        (R := R) k (p ^ e)
    · right
      have hlt : mark < p ^ e := lt_of_le_of_ne hmark_le hexact
      exact ⟨hlt,
        debt_pos_of_mark_lt (p ^ e) mark hlt,
        fun k => transformedMarkedRootIdeal_eq_pivotPower
          (R := R) k (p ^ e) mark⟩
  rankDecrease :=
    PolynomialGraphDebtCausalReentry.rank_decreases
      activeSources (p ^ e) mark hmark_pos hmark_le

/-- The local macro exposes active permissibility. -/
theorem activePermissible
    (h : ι → R)
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    MarkedIdeal.Permissible
      (R := P (R := R) (ι := ι))
      ⟨sourceIdeal h (p ^ e), mark, hmark_pos⟩
      (graphIdeal h) :=
  (certificate (R := R) (ι := ι) (N := N)
    p h boundary hboundary activeSources e mark hmark_pos hmark_le)
      .active.sourcePermissibleAtMark

/-- The local macro exposes passive Tor safety at every centre power. -/
theorem passiveTorSafe
    (h : ι → R)
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark n : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    PolynomialGraphPassiveSafety.TorOneSafeAlong
      (R := R) (ι := ι) (N := N) ((graphIdeal h) ^ n) :=
  (certificate (R := R) (ι := ι) (N := N)
    p h boundary hboundary activeSources e mark hmark_pos hmark_le)
      .passive.allPowerTorSafe n

/-- Every boundary stratum intersects the centre regularly. -/
theorem boundaryStratumRegular
    (h : ι → R)
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (s : Finset β) :
    IsRegularRing
      (P (R := R) (ι := ι) ⧸
        PolynomialGraphBoundaryStrata.graphStratumIdeal h boundary s) :=
  (certificate (R := R) (ι := ι) (N := N)
    p h boundary hboundary activeSources e mark hmark_pos hmark_le)
      .boundaryStrata.regular s

end

end PolynomialGraphLocalResolutionMacro
end Experimental
end PCRLean
