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

/-!
# Integrated graded Frobenius heredity index

This file has no new mathematical assumptions. Its purpose is to force one
Lean build through the complete current experimental heredity chain:

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
* exact commutation with coordinate controlled transforms;
* exact classification of graph-root residuals as a pure exceptional power; and
* actual proper finite-type regular polynomial graph centres with explicit
  all-chart terminal root packets.

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
