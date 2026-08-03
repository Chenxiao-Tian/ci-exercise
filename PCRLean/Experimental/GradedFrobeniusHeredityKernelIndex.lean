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
import PCRLean.Experimental.CoordinateControlledTransformHeredity

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
* the graded-layer sufficient condition;
* actual normal-cone quotient layers and coordinate nonvanishing;
* faithfully flat descent and local coordinate-model compilation; and
* exact commutation of prime-power compression with coordinate controlled
  transforms.

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
