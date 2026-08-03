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

/-!
# Integrated graded Frobenius heredity index

This file has no new mathematical assumptions. Its purpose is to force one
Lean build through the complete current experimental graph-chamber chain:

* exact order scaling for prime powers;
* necessary mark scaling and universal marked equivalence;
* actual point and positive-dimensional centre ideals;
* affine and linear-frame transport;
* exact coordinate-centre root reflection;
* the Frobenius-normal centre interface;
* the nonreduced dual-number no-go;
* the graded-layer and normal-cone sufficient conditions;
* faithfully flat descent and local coordinate/graph models;
* arbitrary-mark ceiling compression and bounded exceptional debt;
* exact controlled transforms and pure exceptional residual classification;
* actual proper finite-type regular polynomial graph centres;
* induced-flat passive Tor safety and flat centre restriction;
* exact regular intersection with every finite coefficient-boundary stratum;
* exact transport of ordered boundary regular sequences, providing the local
  non-zero-divisor/codimension part of the SNC gate;
* source-conservative classification of graph debt as cleanup, not birth; and
* one complete local resolution macro exposing terminality or strict causal
  rank decrease on every standard chart.

The index is experimental and does not assert general resolution.
-/

namespace PCRLean
namespace Experimental
namespace GradedFrobeniusHeredityKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end GradedFrobeniusHeredityKernelIndex
end Experimental
end PCRLean
