import PCRLean.Experimental.IntrinsicKernelIdealFunctoriality
import PCRLean.Experimental.IntrinsicKernelIdealMonotonicity
import PCRLean.Experimental.IntrinsicKernelIdealExactSquare
import PCRLean.Experimental.IntrinsicKernelRootPacket
import PCRLean.Experimental.IntrinsicKernelRootPacketExactSquare
import PCRLean.Experimental.FiniteDimensionalSymmetricRegularBridge
import PCRLean.Experimental.DualPacketRegularCentre
import PCRLean.Experimental.DualPacketRootPackage
import PCRLean.Experimental.NoetherianOrbitDualRegularCentre
import PCRLean.Experimental.MultiOwnerDualFrobeniusChamber
import PCRLean.Experimental.NoetherianOrbitMultiOwnerDualChamber
import PCRLean.Experimental.DualPacketExactTransport
import PCRLean.Experimental.DualPacketBoundaryTransversality
import PCRLean.Experimental.AbstractRootChartTerminality
import PCRLean.Experimental.CoordinateRootChartInstance
import PCRLean.Experimental.CausalBirthLedger
import PCRLean.Experimental.NoetherianCentreWordStack

/-!
# Certified dual-packet resolution-kernel index

This index imports the tangent/cotangent-corrected experimental kernel.  It
certifies the following conditional algebraic architecture:

* a represented Noetherian operator orbit has a finite raw covector packet;
* the packet row span defines an actual proper finite-type regular centre in
  the cotangent symmetric algebra;
* its common tangent kernel is the persistent annihilator of the infinite
  orbit;
* the correctly oriented root package is marked permissible for that centre;
* under the joint-core root-realization equality, the same centre is
  permissible for all active owners and their union;
* exact row-span transport reproduces both centre and root package;
* minimal pivot-root chart data force all-chart terminality;
* a no-recharge finite source ledger plus local rank is well founded;
* Noetherian memory plus finite centre-word replacement is well founded.

The index does not claim arbitrary-dimensional positive-characteristic
resolution.  Universal operator representation, nonlinear lifting from the
cotangent symmetric algebra, root realization, passive and boundary transport,
geometric construction of exact row-span charts, immediate-defect escape and
finite functorial globalization remain explicit frontiers.
-/

namespace PCRLean.Experimental.DualPacketResolutionKernelIndex

#print axioms PCRLean.Experimental.DualPacketRegularCentre.quotientEquiv
#print axioms PCRLean.Experimental.DualPacketRegularCentre.commonTangentKernel_eq_annihilator
#print axioms PCRLean.Experimental.DualPacketRootPackage.rootPacket_permissible
#print axioms PCRLean.Experimental.NoetherianOrbitDualRegularCentre.exists_certificate
#print axioms PCRLean.Experimental.MultiOwnerDualFrobeniusChamber.certificate
#print axioms PCRLean.Experimental.NoetherianOrbitMultiOwnerDualChamber.exists_certificate
#print axioms PCRLean.Experimental.DualPacketExactTransport.map_centre_and_root_eq
#print axioms PCRLean.Experimental.DualPacketBoundaryTransversality.Certificate.mixed_relation_coefficients_zero
#print axioms PCRLean.Experimental.AbstractRootChartTerminality.RootChart.transformedRootIdeal_eq_top
#print axioms PCRLean.Experimental.CoordinateRootChartInstance.transformedRootIdeal_eq_top
#print axioms PCRLean.Experimental.CausalBirthLedger.no_infinite_execution
#print axioms PCRLean.Experimental.NoetherianCentreWordStack.PatchedProgram.no_infinite_execution

end PCRLean.Experimental.DualPacketResolutionKernelIndex
