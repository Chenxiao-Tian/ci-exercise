import Mathlib
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate
import PCRLean.Experimental.PolynomialGraphBoundarySNC
import PCRLean.Experimental.FlatPassiveTorSafety
import PCRLean.Experimental.GraphDebtCleanupCompiler

/-!
# Joint local resolution chamber for polynomial graph centres

This module assembles the strongest current local chamber around one polynomial
graph centre.  Over a finite passive polynomial ring over a field, and for a
nonempty finite normal-coordinate family, the certificate contains:

* one actual, nonempty, nonwhole, finite-type centre ideal;
* an exact regular quotient by the centre;
* Frobenius-normality of the centre filtration;
* marked permissibility for a graph-root packet at every positive mark below
  its prime-power block;
* first-Tor safety for every flat passive owner;
* a boundary frame separated from the centre directions and fixed on every
  standard chart;
* exact factorization on every standard blowup chart;
* terminality at the exact mark, or a pure exceptional debt at a strict
  submark; and
* compilation of that debt into a source-preserving, strictly decreasing
  cleanup step rather than a fresh birth.

This closes a substantial affine chamber.  It still does not provide a general
étale graph atlas, overlap localizations, nonflat passive safety, reconstruction
of the next differential Rees packet, or global serialization.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphJointResolutionChamber

noncomputable section

universe u v w x y z

variable {K : Type u} [Field K]
variable {β : Type v} {α : Type w} {ι : Type x}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {Passive : Type y}
variable {Source : Type z} [Fintype Source] [DecidableEq Source]

abbrev R := MvPolynomial α K
abbrev P := MvPolynomial ι (R (K := K) (α := α))

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphMarkedTransformDebt
open ExceptionalDebtLineage
open GraphDebtCleanupCompiler

variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- Complete local chamber certificate. -/
structure Certificate
    (F : CoordinateBoundarySNC.Frame (β := β) (α := α))
    (h : ι → R (K := K) (α := α))
    (e mark : Nat)
    (passive : Passive → Type u)
    [∀ o, AddCommGroup (passive o)]
    [∀ o, Module (P (K := K) (α := α) (ι := ι)) (passive o)]
    (eventSource : Source)
    (baseActive : Finset (Finset Source)) where
  mark_pos : 0 < mark
  mark_le_block : mark ≤ p ^ e
  centre :
    PolynomialGraphFrobeniusCentreCertificate.Certificate p h e
  arbitraryMark :
    PolynomialGraphArbitraryMarkCertificate.Certificate p h e mark
  boundary :
    PolynomialGraphBoundarySNC.Certificate (K := K) (ι := ι) F h
  passiveTorSafe : ∀ o : Passive,
    FlatPassiveTorSafety.TorSafe (graphIdeal h) (passive o)
  debtEvent : Event (Source := Source)
  debtEvent_eq : debtEvent =
    graphEvent eventSource (p ^ e) mark mark_pos mark_le_block
  cleanup :
    CausalEventLedger.Step
      (parentState debtEvent baseActive)
      (childState debtEvent baseActive)
  chartResidual : ∀ k : ι,
    transformedMarkedRootIdeal
        (R := R (K := K) (α := α)) k (p ^ e) mark =
      (pivotIdeal (R := R (K := K) (α := α)) k) ^
        (childState debtEvent baseActive).cleanupHeight
  noFreshBirthSameSource :
    ¬ Disjoint debtEvent.support
      (parentState debtEvent baseActive).used

/-- Assemble the complete graph-centre chamber. -/
noncomputable def certificate
    (F : CoordinateBoundarySNC.Frame (β := β) (α := α))
    (h : ι → R (K := K) (α := α))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (passive : Passive → Type u)
    [∀ o, AddCommGroup (passive o)]
    [∀ o, Module (P (K := K) (α := α) (ι := ι)) (passive o)]
    [∀ o, Module.Flat
      (P (K := K) (α := α) (ι := ι)) (passive o)]
    (eventSource : Source)
    (baseActive : Finset (Finset Source)) :
    Certificate p F h e mark passive eventSource baseActive where
  mark_pos := hmark_pos
  mark_le_block := hmark_le
  centre :=
    PolynomialGraphFrobeniusCentreCertificate.certificate p h e
  arbitraryMark :=
    PolynomialGraphArbitraryMarkCertificate.certificate
      p h e mark hmark_pos hmark_le
  boundary :=
    PolynomialGraphBoundarySNC.certificate F h
  passiveTorSafe :=
    FlatPassiveTorSafety.owners_torSafe_of_flat passive (graphIdeal h)
  debtEvent :=
    graphEvent eventSource (p ^ e) mark hmark_pos hmark_le
  debtEvent_eq := rfl
  cleanup :=
    GraphDebtCleanupCompiler.cleanupStep
      (graphEvent eventSource (p ^ e) mark hmark_pos hmark_le)
      baseActive
  chartResidual := by
    intro k
    exact GraphDebtCleanupCompiler.graphResidualIdeal_eq_childHeight
      (R := R (K := K) (α := α))
      eventSource (p ^ e) mark hmark_pos hmark_le baseActive k
  noFreshBirthSameSource :=
    GraphDebtCleanupCompiler.not_fresh_birth_same_support
      (graphEvent eventSource (p ^ e) mark hmark_pos hmark_le)
      baseActive

/-- The local cleanup transition strictly lowers the concrete causal rank. -/
theorem cleanup_rank_decreases
    (F : CoordinateBoundarySNC.Frame (β := β) (α := α))
    (h : ι → R (K := K) (α := α))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (eventSource : Source)
    (baseActive : Finset (Finset Source)) :
    GenRank.Lt
      (childState
        (graphEvent eventSource (p ^ e) mark hmark_pos hmark_le)
        baseActive).rank
      (parentState
        (graphEvent eventSource (p ^ e) mark hmark_pos hmark_le)
        baseActive).rank :=
  GraphDebtCleanupCompiler.rank_decreases
    (graphEvent eventSource (p ^ e) mark hmark_pos hmark_le)
    baseActive

end

end PolynomialGraphJointResolutionChamber
end Experimental
end PCRLean
