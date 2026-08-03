import Mathlib
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate
import PCRLean.Experimental.PolynomialGraphBoundaryStratum

/-!
# Combined graph-centre, Frobenius and boundary certificate

This module combines the strongest current affine graph-centre outputs without
silently merging their meanings.  Over a Noetherian regular domain it records:

* an actual proper finite-type graph centre with regular quotient;
* Frobenius-normality and arbitrary-mark active permissibility;
* every standard chart, terminal at the exact Frobenius mark and otherwise a
  pure bounded exceptional debt;
* a proper regular scheme-theoretic intersection with a chosen coefficient
  boundary stratum; and
* ideal-theoretic first-order transversality `I_h ⊓ J A = I_h * J A`.

This is not yet a full SNC or joint-legality certificate.  Local freeness of
the conormal direct sum, codimension additivity, passive Tor safety, overlap
descent and hereditary packet reconstruction remain explicit separate fields
of the general theorem.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBoundaryFrobeniusCertificate

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [IsNoetherianRing R] [IsRegularRing R]

open PolynomialGraphCentreHeredity
open PolynomialGraphArbitraryMarkCertificate
open PolynomialGraphBoundaryStratum
open BoundaryTransversalityGate

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- The combined local chamber certificate. -/
structure Certificate
    (h : ι → R) (J : Ideal R) (e mark : Nat) where
  activeCentre :
    PolynomialGraphArbitraryMarkCertificate.Certificate p h e mark
  boundaryStratum :
    PolynomialGraphBoundaryStratum.Certificate h J
  centreBoundaryTransverse :
    Transverse (graphIdeal h) (J.map MvPolynomial.C)

/-- Assemble the combined certificate from a regular proper boundary stratum. -/
noncomputable def certificate
    (h : ι → R) (J : Ideal R)
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (hJ : J ≠ ⊤)
    [IsRegularRing (R ⧸ J)] :
    Certificate p h J e mark where
  activeCentre :=
    PolynomialGraphArbitraryMarkCertificate.certificate
      p h e mark hmark_pos hmark_le
  boundaryStratum :=
    PolynomialGraphBoundaryStratum.certificate h J hJ
  centreBoundaryTransverse :=
    PolynomialGraphBoundaryStratum.graphIdeal_transverse_mappedBoundary h J

end

end PolynomialGraphBoundaryFrobeniusCertificate
end Experimental
end PCRLean
