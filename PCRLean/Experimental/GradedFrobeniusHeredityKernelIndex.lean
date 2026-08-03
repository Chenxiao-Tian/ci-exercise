import PCRLean.Experimental.UnivariateFrobeniusOrderHeredity
import PCRLean.Experimental.FrobeniusMarkScalingBoundary
import PCRLean.Experimental.UnivariateOrderBaseChange
import PCRLean.Experimental.UniversalMarkedFrobeniusEquivalence
import PCRLean.Experimental.MultivariateFrobeniusOrderHeredity
import PCRLean.Experimental.MultivariateOrderIdealBridge
import PCRLean.Experimental.MultivariatePointIdealBridge
import PCRLean.Experimental.CoordinateSubspaceOrderHeredity
import PCRLean.Experimental.AffineCoordinateSubspaceHeredity
import PCRLean.Experimental.LinearFrameSubspaceHeredity
import PCRLean.Experimental.FrobeniusSupportDomain
import PCRLean.Experimental.CoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.AffineLinearFrameExactFrobeniusHeredity
import PCRLean.Experimental.FrobeniusNormalCentre
import PCRLean.Experimental.FrobeniusNormalCentreCounterexample
import PCRLean.Experimental.GradedPowerReflection
import PCRLean.Experimental.NormalConeLayer
import PCRLean.Experimental.CoordinateNormalConeFrobeniusReduced
import PCRLean.Experimental.FrobeniusNormalFaithfullyFlatDescent
import PCRLean.Experimental.FrobeniusNormalLocalCoordinateModel
import PCRLean.Experimental.FrobeniusNormalTransport
import PCRLean.Experimental.CeilingMarkedPowerReflection
import PCRLean.Experimental.ControlledFrobeniusTransform
import PCRLean.Experimental.CeilingControlledTransformDebt
import PCRLean.Experimental.CoordinateControlledTransformHeredity
import PCRLean.Experimental.PolynomialGraphCentreHeredity
import PCRLean.Experimental.PolynomialGraphCentreQuotient
import PCRLean.Experimental.PolynomialGraphBlowupHeredity
import PCRLean.Experimental.PolynomialGraphMarkedTransformDebt
import PCRLean.Experimental.PolynomialGraphFrobeniusCentreCertificate
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate
import PCRLean.Experimental.PolynomialGraphPassiveSafety
import PCRLean.Experimental.PolynomialGraphBoundaryIntersection
import PCRLean.Experimental.PolynomialGraphBoundaryStrata
import PCRLean.Experimental.PolynomialGraphBoundaryRegularSequence
import PCRLean.Experimental.PolynomialGraphJointLegalityCertificate
import PCRLean.Experimental.PolynomialGraphSupportEquality
import PCRLean.Experimental.PolynomialGraphActionBoundary
import PCRLean.Experimental.CausalEventLedger
import PCRLean.Experimental.PolynomialGraphDebtCausalReentry
import PCRLean.Experimental.PolynomialGraphLocalResolutionMacro
import PCRLean.Experimental.FittingMinorAtlas
import PCRLean.Experimental.FittingMinorFaithfulCover
import PCRLean.Experimental.FittingGraphCentreAtlas
import PCRLean.Experimental.PolynomialGraphBaseChange
import PCRLean.Experimental.FittingGraphCentreOverlap
import PCRLean.Experimental.FittingGraphCechEffectivity
import PCRLean.Experimental.FittingGraphSectionAtlas
import PCRLean.Experimental.FittingGraphRestrictionCompatibility
import PCRLean.Experimental.FittingGraphGlobalResolutionMacro
import PCRLean.Experimental.InvertibleLinearSystemGraph
import PCRLean.Experimental.DetUnitLinearSystemGraph
import PCRLean.Experimental.FittingLinearSystemAtlas
import PCRLean.Experimental.FittingLinearSystemOverlap
import PCRLean.Experimental.FittingLinearSystemGlobalResolutionMacro
import PCRLean.Experimental.FittingLinearSystemRowCompatibility
import PCRLean.Experimental.FittingLinearSystemRowGlobalResolutionMacro
import PCRLean.Experimental.FittingLinearSystemCommonPacket
import PCRLean.Experimental.AugmentedMinorConsistency
import PCRLean.Experimental.AugmentedMinorRangeNecessity
import PCRLean.Experimental.FittingAugmentedMinorConsistency
import PCRLean.Experimental.FittingAugmentedMinorGlobalResolutionMacro
import PCRLean.Experimental.MaximalMinorAtlas
import PCRLean.Experimental.MaximalMinorCommonPacket
import PCRLean.Experimental.MaximalMinorAugmentedPacket
import PCRLean.Experimental.MaximalMinorRangeCriterion
import PCRLean.Experimental.MaximalMinorGlobalResolutionMacro
import PCRLean.Experimental.MaximalMinorPresentationIndependence

/-!
# Integrated graded Frobenius heredity index

This file has no new mathematical assumptions. Its purpose is to force one
Lean build through the complete current experimental affine centre-synthesis
chain:

* exact order scaling for prime powers and arbitrary-mark ceiling compression;
* Frobenius-normal centre filtrations and normal-cone nonvanishing;
* actual proper finite-type regular polynomial graph centres;
* exact reduced support of the graph-root packet;
* explicit separation of the principal Cartier action boundary;
* active, induced-flat passive and SNC-sequence legality;
* all standard controlled-transform charts;
* pure exceptional debt classified as source-conservative cleanup;
* finite determinant basic-open covers;
* jointly faithful equality reflection on those covers;
* affine structure-sheaf Čech effectivity and exact global graph ideals;
* determinant-unit affine systems and presentation-independent common packets;
* the Schur augmented-minor consistency theorem;
* necessity of augmented-minor vanishing for every actual solution;
* the exact maximal-minor range criterion:
  maximal minors generate one and augmented minors vanish iff the rectangular
  packet has a unique solution;
* invariance of that criterion and of the global graph under intrinsic changes
  of equation frame; and
* one canonical global affine resolution macro obtained directly from the two
  finite determinantal conditions.

The remaining universal work is to extract the finite rectangular packet and
the two determinantal identities from an arbitrary intrinsic
Frobenius--Hasse state, prove a genuine nonidentity action in the higher-rank
scheme chamber, reconstruct the next state hereditarily, treat immediate
defect, and serialize globally. The index is experimental and does not assert
general resolution.
-/

namespace PCRLean
namespace Experimental
namespace GradedFrobeniusHeredityKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end GradedFrobeniusHeredityKernelIndex
end Experimental
end PCRLean
