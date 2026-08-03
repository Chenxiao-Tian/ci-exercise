import PCRLean.Experimental.DualPacketAffineLinearRealization
import PCRLean.Experimental.DualPacketAffineQuotient
import PCRLean.Experimental.DualPacketAffineRootPackage
import PCRLean.Experimental.FrobeniusFiniteRootGeneration
import PCRLean.Experimental.NoetherianOrbitPacketCanonicity
import PCRLean.Experimental.NoetherianOrbitCanonicalFrobeniusAffineChamber
import PCRLean.Experimental.DualPacketCoordinateNormalization
import PCRLean.Experimental.DualPacketBlowupChart
import PCRLean.Experimental.NoetherianOrbitCanonicalFrobeniusBlowupChamber
import PCRLean.Experimental.DualPacketRankZeroNoGo
import PCRLean.Experimental.PerfectFrobeniusRankZeroEscape
import PCRLean.Experimental.PerfectFrobeniusPureIdealEscape
import PCRLean.Experimental.MultiOwnerPerfectFrobeniusEscapeChamber
import PCRLean.Experimental.PerfectFrobeniusFinitePresentation
import PCRLean.Experimental.MultiOwnerPerfectFrobeniusPresentationChamber
import PCRLean.Experimental.DualPacketExactTransport
import PCRLean.Experimental.DualPacketBoundaryTransversality
import PCRLean.Experimental.CausalBirthLedger
import PCRLean.Experimental.NoetherianCentreWordStack

/-!
# Integrated canonical Frobenius blowup-kernel index

This index is the strongest current tangent/cotangent-corrected local formal
kernel.

Certified positive-rank chamber:

* a represented Noetherian operator orbit has a packet-choice-independent
  actual affine centre and a canonical finite `p^e` packet-power ideal;
* one canonical finite joint-core equality yields an actual proper finite-type
  regular centre permissible for every active owner and their union;
* positive row-span rank yields an explicit basis normalization, actual
  conjugated blowup charts, exact exceptional factorization, and all-chart
  terminality of the full controlled root packet.

Certified rank-zero analysis:

* the current linear packet has zero row span, zero actual centre, zero root
  ideal and no pivot, so repetition of that packet cannot progress;
* over a perfect field, any nonzero finite pure Frobenius presentation admits a
  finite covector root packet of positive rank and enters the certified blowup
  chamber.

Additional certified interfaces include exact row-span transport, first-order
boundary transversality, a no-recharge causal birth ledger, and Noetherian
centre-word multiset termination.

This index does not prove arbitrary-dimensional positive-characteristic
resolution.  Universal operator representation, canonical finite root
realization for arbitrary prepared singularities, imperfect-field and mixed
rank-zero escape, nonlinear local-to-global lifting, passive/boundary hereditary
transport, immediate-defect escape and finite functorial globalization remain
explicit frontiers.
-/

namespace PCRLean.Experimental.CanonicalFrobeniusBlowupKernelIndex

#print axioms PCRLean.Experimental.DualPacketAffineQuotient.ker_actualProjectAlg_eq_actualIdeal
#print axioms PCRLean.Experimental.DualPacketAffineQuotient.quotient_isRegularRing
#print axioms PCRLean.Experimental.FrobeniusFiniteRootGeneration.actualRootPowerIdeal_eq_packetPowerIdeal
#print axioms PCRLean.Experimental.NoetherianOrbitPacketCanonicity.packetPowerIdeal_eq_canonical
#print axioms PCRLean.Experimental.NoetherianOrbitCanonicalFrobeniusAffineChamber.certificate
#print axioms PCRLean.Experimental.DualPacketCoordinateNormalization.map_actualIdeal_eq_coordinateCentreIdeal
#print axioms PCRLean.Experimental.DualPacketBlowupChart.basisGenerator_pow_factorization
#print axioms PCRLean.Experimental.DualPacketBlowupChart.transformedRootIdeal_eq_top
#print axioms PCRLean.Experimental.NoetherianOrbitCanonicalFrobeniusBlowupChamber.certificate
#print axioms PCRLean.Experimental.DualPacketRankZeroNoGo.owner_eq_bot_of_rank_zero_root_realization
#print axioms PCRLean.Experimental.PerfectFrobeniusRankZeroEscape.rootLinearPolynomial_pow
#print axioms PCRLean.Experimental.MultiOwnerPerfectFrobeniusEscapeChamber.certificate
#print axioms PCRLean.Experimental.PerfectFrobeniusFinitePresentation.packetPowerIdeal_eq_purePresentationIdeal
#print axioms PCRLean.Experimental.MultiOwnerPerfectFrobeniusPresentationChamber.certificate
#print axioms PCRLean.Experimental.DualPacketExactTransport.map_centre_and_root_eq
#print axioms PCRLean.Experimental.DualPacketBoundaryTransversality.Certificate.mixed_relation_coefficients_zero
#print axioms PCRLean.Experimental.CausalBirthLedger.no_infinite_execution
#print axioms PCRLean.Experimental.NoetherianCentreWordStack.PatchedProgram.no_infinite_execution

end PCRLean.Experimental.CanonicalFrobeniusBlowupKernelIndex
