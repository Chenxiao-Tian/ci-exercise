import Mathlib
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate
import PCRLean.Experimental.PolynomialGraphPassiveSafety
import PCRLean.Experimental.PolynomialGraphBoundaryIntersection

/-!
# Joint active/passive/boundary legality for a polynomial graph chamber

This module combines three independently proved local gates for the same actual
polynomial graph centre `I_h = (Z_i-h_i)`:

1. **Active legality.**  A prime-power graph-root packet with every positive
   mark `m ≤ p^e` is permissible.  On each standard chart it is terminal at
   `m=p^e` and otherwise leaves exactly the pure exceptional debt
   `(E_k)^(p^e-m)`.
2. **Passive legality.**  Every passive module induced from an `R`-flat module
   is ambient-flat, Tor-safe along every power of `I_h`, and remains flat after
   restriction to the centre.
3. **Boundary legality.**  For every coefficient-ring boundary stratum `J`, the
   scheme-theoretic graph--boundary intersection has exact quotient `R/J`.
   Hence a regular boundary stratum remains regular on the centre.

The resulting certificate closes a substantial joint-legality chamber without
inferring passive or boundary properties from active containment.  It remains
a local affine graph theorem: a general resolution proof must still construct
such models, glue their chart data, handle arbitrary passive modules and prove
scheme-level SNC transversality and hereditary packet reconstruction.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphJointLegalityCertificate

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
variable [IsNoetherianRing R] [IsRegularRing R]

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphBoundaryIntersection

abbrev P := MvPolynomial ι R

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Joint certificate for one graph centre, one active Frobenius packet, one
induced-flat passive datum, and one coefficient boundary stratum. -/
structure Certificate
    (h : ι → R) (J : Ideal R) (e mark : Nat)
    [IsRegularRing (R ⧸ J)] where
  centre : Ideal (P (R := R) (ι := ι))
  centre_eq : centre = graphIdeal h
  actualRegularCentre :
    PolynomialGraphFrobeniusCentreCertificate.Certificate p h e
  active :
    PolynomialGraphArbitraryMarkCertificate.Certificate p h e mark
  passive :
    PolynomialGraphPassiveSafety.Certificate
      (R := R) (ι := ι) (N := N) h
  boundary :
    PolynomialGraphBoundaryIntersection.Certificate h J
  boundaryIntersectionRegular :
    IsRegularRing
      (P (R := R) (ι := ι) ⧸
        PolynomialGraphBoundaryIntersection.combinedIdeal h J)
  chartResidualClassification : ∀ k : ι,
    PolynomialGraphMarkedTransformDebt.transformedMarkedRootIdeal
        (R := R) k (p ^ e) mark =
      (pivotIdeal (R := R) k) ^ (p ^ e - mark)

/-- Assemble the full joint-legality certificate. -/
noncomputable def certificate
    (h : ι → R) (J : Ideal R) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    [IsRegularRing (R ⧸ J)] :
    Certificate (R := R) (ι := ι) (N := N) p h J e mark where
  centre := graphIdeal h
  centre_eq := rfl
  actualRegularCentre :=
    PolynomialGraphFrobeniusCentreCertificate.certificate p h e
  active :=
    PolynomialGraphArbitraryMarkCertificate.certificate
      p h e mark hmark_pos hmark_le
  passive :=
    PolynomialGraphPassiveSafety.certificate
      (R := R) (ι := ι) (N := N) h
  boundary :=
    PolynomialGraphBoundaryIntersection.certificate h J
  boundaryIntersectionRegular :=
    PolynomialGraphBoundaryIntersection.quotient_isRegularRing h J
  chartResidualClassification := fun k =>
    PolynomialGraphMarkedTransformDebt
      .transformedMarkedRootIdeal_eq_pivotPower
        (R := R) k (p ^ e) mark

/-- The certificate exposes Tor safety along every centre power. -/
theorem allPowerTorSafe
    (h : ι → R) (J : Ideal R) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    [IsRegularRing (R ⧸ J)]
    (n : Nat) :
    PolynomialGraphPassiveSafety.TorOneSafeAlong
      (R := R) (ι := ι) (N := N) ((graphIdeal h) ^ n) :=
  (certificate (R := R) (ι := ι) (N := N)
    p h J e mark hmark_pos hmark_le).passive.allPowerTorSafe n

/-- The centre restriction of the passive datum is flat. -/
theorem centreRestrictionFlat
    (h : ι → R) (J : Ideal R) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    [IsRegularRing (R ⧸ J)] :
    Module.Flat (P (R := R) (ι := ι) ⧸ graphIdeal h)
      (PolynomialGraphPassiveSafety.RestrictedPassive
        (R := R) (ι := ι) (N := N) (graphIdeal h)) :=
  (certificate (R := R) (ι := ι) (N := N)
    p h J e mark hmark_pos hmark_le).passive.centreRestrictionFlat

/-- Every chart has either terminality or one explicitly bounded pure
exceptional debt, inherited from the active certificate. -/
theorem terminal_or_positiveDebt
    (h : ι → R) (J : Ideal R) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    [IsRegularRing (R ⧸ J)] :
    mark = p ^ e ∨ 0 < p ^ e - mark :=
  (certificate (R := R) (ι := ι) (N := N)
    p h J e mark hmark_pos hmark_le).active.terminal_or_positiveDebt

end

end PolynomialGraphJointLegalityCertificate
end Experimental
end PCRLean
