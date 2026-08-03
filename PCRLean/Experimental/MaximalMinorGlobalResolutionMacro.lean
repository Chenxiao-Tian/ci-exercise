import Mathlib
import PCRLean.Experimental.MaximalMinorRangeCriterion
import PCRLean.Experimental.FittingAugmentedMinorGlobalResolutionMacro

/-!
# Global affine resolution macro from canonical maximal and augmented minors

For a finite rectangular packet `M z = b`, assume:

* the canonical maximal row minors of `M` generate the unit ideal; and
* every canonical selected-plus-one augmented maximal minor of `[M|b]`
  vanishes.

No chart family, selected subsystem, local graph tuple or overlap certificate is
supplied separately.  These two finite determinantal conditions produce:

* a unique global solution `z`;
* one actual global graph centre;
* exact base change to every selected-minor chart;
* the complete active, induced-flat passive, boundary-sequence, all-chart and
  source-causal graph macro.

This is the strongest current affine compiler from presentation-level
Fitting data to one actual ordinary-centre step.  The remaining universal
bridge is extraction of the rectangular packet and the two determinantal
identities from an arbitrary intrinsic Frobenius--Hasse state.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorGlobalResolutionMacro

noncomputable section

universe u v w x y z

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsNoetherianRing R] [IsRegularRing R]
variable {κ : Type v} [Fintype κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {N : Type x} [AddCommGroup N] [Module R N] [Module.Flat R N]
variable {β : Type y} [Fintype β] [DecidableEq β]
variable {Source : Type z} [Fintype Source] [DecidableEq Source]

open MaximalMinorAtlas
open MaximalMinorAugmentedPacket

variable (M : Matrix κ ι R)
variable (b : κ → R)
variable (Hrank : FullRankCover M)
variable (Haug : AugmentedRankCondition M b)
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Canonical localized augmented-minor certificate. -/
noncomputable def localizedAugmentedCertificate :
    FittingAugmentedMinorConsistency.AugmentedMinorsVanish
      (MaximalMinorCommonPacket.data M b Hrank) :=
  Haug.toAugmentedMinorsVanish Hrank

/-- The determinantal solution. -/
noncomputable def globalGraph : ι → R :=
  Haug.globalGraph Hrank

/-- The actual global graph centre. -/
def globalCentre : Ideal (MvPolynomial ι R) :=
  PolynomialGraphCentreHeredity.graphIdeal (Haug.globalGraph Hrank)

/-- Full canonical maximal-minor certificate. -/
structure Certificate
    (boundary : β → Ideal R)
    (activeSources : Finset (Finset Source))
    (e mark : Nat) where
  rangeCriterion :
    ∃! g : ι → R, M.mulVec g = b
  globalGraph : ι → R
  globalEquation : M.mulVec globalGraph = b
  globalCentre : Ideal (MvPolynomial ι R)
  centre_eq : globalCentre =
    PolynomialGraphCentreHeredity.graphIdeal globalGraph
  globalMacro :
    FittingAugmentedMinorGlobalResolutionMacro.Certificate
      (R := R) (N := N)
      (Haug.toAugmentedMinorsVanish Hrank) p
      boundary activeSources e mark

/-- Assemble the complete affine resolution macro directly from the two
canonical determinantal conditions. -/
noncomputable def certificate
    (boundary : β → Ideal R)
    (hboundary :
      PolynomialGraphBoundaryStrata.RegularBoundaryFamily boundary)
    (activeSources : Finset (Finset Source))
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e) :
    Certificate (R := R) (N := N)
      M b Hrank Haug p boundary activeSources e mark where
  rangeCriterion := Haug.existsUnique_solution Hrank
  globalGraph := Haug.globalGraph Hrank
  globalEquation := Haug.globalGraph_solves Hrank
  globalCentre := globalCentre M b Hrank Haug
  centre_eq := rfl
  globalMacro :=
    FittingAugmentedMinorGlobalResolutionMacro.certificate
      (R := R) (N := N)
      (Haug.toAugmentedMinorsVanish Hrank) p
      boundary hboundary activeSources e mark
      hmark_pos hmark_le

/-- Every selected subsystem ideal is the base change of the same actual global
centre. -/
theorem allLocalSystemIdeals_fromGlobal
    (s : Selection (κ := κ) (ι := ι)) :
    ((MaximalMinorCommonPacket.data M b Hrank).toSystemAtlas.localSystem s)
        .equationIdeal =
      Ideal.map
        (PolynomialGraphBaseChange.polynomialMap
          (ι := ι)
          (algebraMap R
            (FittingGraphCentreAtlas.ChartRing Hrank.toAtlas s)))
        (globalCentre M b Hrank Haug) :=
  (Haug.toAugmentedMinorsVanish Hrank)
    .localEquationIdeal_is_globalCentreBaseChange s

/-- The determinantal solution is independent of every selected-minor chart. -/
theorem globalGraph_localizes
    (s : Selection (κ := κ) (ι := ι)) (i : ι) :
    algebraMap R
        (FittingGraphCentreAtlas.ChartRing Hrank.toAtlas s)
        (globalGraph M b Hrank Haug i) =
      (MaximalMinorCommonPacket.data M b Hrank).graph s i :=
  Haug.globalGraph_localizes Hrank s i

end

end MaximalMinorGlobalResolutionMacro
end Experimental
end PCRLean
