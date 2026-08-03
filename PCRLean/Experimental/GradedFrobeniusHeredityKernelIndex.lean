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
import PCRLean.Experimental.CausalEventLedger
import PCRLean.Experimental.PolynomialGraphDebtCausalReentry
import PCRLean.Experimental.PolynomialGraphLocalResolutionMacro
import PCRLean.Experimental.FittingMinorAtlas
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

/-!
# Integrated graded Frobenius heredity index

This file has no new mathematical assumptions. Its purpose is to force one
Lean build through the complete current experimental affine graph-centre chain:

* exact order scaling for prime powers and arbitrary-mark ceiling compression;
* Frobenius-normal centre filtrations and normal-cone nonvanishing;
* actual proper finite-type regular graph centres;
* active, induced-flat passive and SNC-sequence legality;
* all standard controlled-transform charts;
* pure exceptional debt classified as source-conservative cleanup;
* finite determinant basic-open covers;
* affine structure-sheaf Čech effectivity and exact global graph ideals;
* an exact ideal equality converting an invertible affine linear system into
  the graph of its unique solution;
* automatic inversion from a determinant-unit minor;
* one determinant-normalized system on every Fitting chart;
* automatic graph overlap compatibility from equality of the matrices and
  right-hand sides on double localizations; and
* one actual global affine graph centre and complete global resolution macro,
  with no graph tuple or centre ideal supplied independently.

Conditional on extracting a finite compatible determinant-normalized linear
system atlas from the intrinsic Frobenius/Hasse/Fitting state, the entire affine
actual-centre, joint-legality, chart, Čech and causal macro is closed in the
stated chamber. The remaining universal work is that extraction theorem,
hereditary next-state reconstruction, immediate defect, and non-affine global
serialization. The index is experimental and does not assert general
resolution.
-/

namespace PCRLean
namespace Experimental
namespace GradedFrobeniusHeredityKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end GradedFrobeniusHeredityKernelIndex
end Experimental
end PCRLean
