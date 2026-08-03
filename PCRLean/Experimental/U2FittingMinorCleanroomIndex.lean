import PCRLean.Experimental.CausalEventPacking
import PCRLean.Experimental.LinearSplitCentreQuotient
import PCRLean.Experimental.SplitSurjectionSymmetricQuotient
import PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient
import PCRLean.Experimental.SurjectiveFreeRegularCentre
import PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular
import PCRLean.Experimental.BiorthogonalRegularCentre
import PCRLean.Experimental.InvertibleMinorRegularCentre
import PCRLean.Experimental.IntrinsicCentreGaugeInvariance

/-!
# U2 Fitting-minor clean-room index

This isolated target forces the current intrinsic-centre chain through Lean.
It is not imported by the official MLE–Lean baseline and does not state a
general resolution theorem.  The exact theorem boundary is an invertible local
evaluation minor, not an arbitrary positive-characteristic singularity.
-/

namespace PCRLean.Experimental.U2FittingMinorCleanroomIndex

#print axioms PCRLean.Experimental.CausalEventPacking.Section.card_events_le_card_sources
#print axioms PCRLean.Experimental.LinearSplitCentreQuotient.quotientEquiv
#print axioms PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.quotientEquiv
#print axioms PCRLean.Experimental.SurjectiveLinearMapSymmetricQuotient.quotientEquiv
#print axioms PCRLean.Experimental.SurjectiveFreeRegularCentre.certificate
#print axioms PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular.finiteType
#print axioms PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular.isNoetherianRing
#print axioms PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular.isRegularRing
#print axioms PCRLean.Experimental.BiorthogonalRegularCentre.finiteDimensionalCertificate
#print axioms PCRLean.Experimental.InvertibleMinorRegularCentre.MinorCertificate.finiteDimensionalCertificate
#print axioms PCRLean.Experimental.IntrinsicCentreGaugeInvariance.GaugeAtlas.kernelIdeal_eq

end PCRLean.Experimental.U2FittingMinorCleanroomIndex
