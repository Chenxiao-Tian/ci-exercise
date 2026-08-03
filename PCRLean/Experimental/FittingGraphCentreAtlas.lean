import Mathlib
import Mathlib.RingTheory.Localization.Away.Basic
import PCRLean.Experimental.FittingMinorAtlas
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate

/-!
# Fitting determinant atlases with actual graph centres

Let `R` be a Noetherian regular domain of characteristic `p`. A finite family of
Fitting determinants generating the unit ideal gives a finite principal-open
cover of `Spec R`. On the chart away from one determinant, attach an actual
polynomial graph presentation.

The localization remains a Noetherian regular domain, so the graph presentation
compiles to an actual proper finite-type regular centre with arbitrary-mark
Frobenius heredity and every standard chart.

This module therefore turns the finite determinant cover into a finite atlas of
fully certified *local candidate centres*. It does not yet glue those centres
on chart overlaps or prove that an arbitrary Frobenius/Fitting core supplies
the required graph presentations. Those are the exact remaining U2/U3 bridge
theorems.
-/

namespace PCRLean
namespace Experimental
namespace FittingGraphCentreAtlas

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Canonical coefficient ring on one determinant chart. -/
abbrev ChartRing
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (c : Chart) := Localization.Away (A.determinant c)

/-- A graph presentation attached to every determinant chart. -/
structure GraphAtlasData
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)) where
  graph : ∀ c : Chart, ι → ChartRing A c

namespace GraphAtlasData

variable {A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart)}
    (D : GraphAtlasData (ι := ι) A)

/-- Every determinant chart has an actual regular graph-centre certificate. -/
noncomputable def localCentreCertificate
    (c : Chart) (e : Nat) :
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (D.graph c) e :=
  PolynomialGraphFrobeniusCentreCertificate.certificate
    p (D.graph c) e

/-- Arbitrary positive marks below the Frobenius block are also compiled. -/
noncomputable def localArbitraryMarkCertificate
    (c : Chart) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    PolynomialGraphArbitraryMarkCertificate.Certificate
      p (D.graph c) e mark :=
  PolynomialGraphArbitraryMarkCertificate.certificate
    p (D.graph c) e mark hmark_pos hmark_le

/-- The distinguished determinant is a unit on its graph-centre chart. -/
theorem determinant_isUnit (c : Chart) :
    IsUnit
      (algebraMap R (ChartRing A c) (A.determinant c)) :=
  A.determinant_isUnit_away c

/-- Every prime point is covered by a chart carrying an actual regular graph
centre. -/
theorem point_has_graph_chart
    (x : PrimeSpectrum R) :
    ∃ c : Chart,
      x ∈ PrimeSpectrum.basicOpen (A.determinant c) ∧
      Nonempty
        (PolynomialGraphFrobeniusCentreCertificate.Certificate
          p (D.graph c) 0) := by
  rcases A.point_mem_some_basicOpen x with ⟨c, hc⟩
  exact ⟨c, hc, ⟨D.localCentreCertificate p c 0⟩⟩

/-- Finite local-centre atlas certificate. -/
structure Certificate (e mark : Nat) where
  cover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤
  localCentre : ∀ c : Chart,
    PolynomialGraphFrobeniusCentreCertificate.Certificate
      p (D.graph c) e
  localArbitraryMark : 0 < mark → mark ≤ p ^ e → ∀ c : Chart,
    PolynomialGraphArbitraryMarkCertificate.Certificate
      p (D.graph c) e mark
  determinantUnit : ∀ c : Chart,
    IsUnit (algebraMap R (ChartRing A c) (A.determinant c))

/-- Assemble the finite local graph-centre atlas. -/
noncomputable def certificate
    (e mark : Nat) : Certificate p D e mark where
  cover := A.basicOpen_cover
  localCentre := fun c => D.localCentreCertificate p c e
  localArbitraryMark := fun hpos hle c =>
    D.localArbitraryMarkCertificate p c e mark hpos hle
  determinantUnit := D.determinant_isUnit p

end GraphAtlasData

end

end FittingGraphCentreAtlas
end Experimental
end PCRLean
