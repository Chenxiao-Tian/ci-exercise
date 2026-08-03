import PCRLean.Experimental.DeterminantMinorRegularCentre
import PCRLean.Experimental.IntrinsicKernelIdealEquiv
import PCRLean.Experimental.IntrinsicKernelIdealComposition
import PCRLean.Experimental.IntrinsicKernelIdealBiEquiv
import PCRLean.Experimental.FittingAwayRegularCentre
import PCRLean.Experimental.FittingMinorCover
import PCRLean.Experimental.RangeRestrictedRegularCentre
import PCRLean.Experimental.CausalEventTransport
import PCRLean.Experimental.CausalBudgetCompiler

/-!
# U2 range/Fitting/equivariance and U6 causal index

This isolated target forces the current intrinsic-centre reduction and causal
termination slice through Lean. It is experimental and is not imported by the
official MLE–Lean baseline. In particular it does not assert universal
Frobenius packet realization, image-local-freeness, localization descent,
hereditary blowup transport, globalization, or the general resolution theorem.
-/

namespace PCRLean.Experimental.U2EquivCausalIndex

#print axioms PCRLean.Experimental.DeterminantMinorRegularCentre.finiteFreeCertificate
#print axioms PCRLean.Experimental.IntrinsicKernelIdealEquiv.map_kernelIdeal_eq
#print axioms PCRLean.Experimental.IntrinsicKernelIdealComposition.kernelIdeal_le_comp
#print axioms PCRLean.Experimental.IntrinsicKernelIdealComposition.kernelIdeal_comp_equiv
#print axioms PCRLean.Experimental.IntrinsicKernelIdealBiEquiv.map_kernelIdeal_eq
#print axioms PCRLean.Experimental.FittingAwayRegularCentre.mapped_det_isUnit
#print axioms PCRLean.Experimental.FittingAwayRegularCentre.finiteFreeCertificate
#print axioms PCRLean.Experimental.FittingMinorCover.Cover.exists_det_not_mem_prime
#print axioms PCRLean.Experimental.RangeRestrictedRegularCentre.kernelIdeal_rangeProject_eq
#print axioms PCRLean.Experimental.RangeRestrictedRegularCentre.finiteFreeCertificate
#print axioms PCRLean.Experimental.RangeRestrictedRegularCentre.finiteDimensionalCertificate
#print axioms PCRLean.Experimental.CausalEventTransport.Transport.parent_injective
#print axioms PCRLean.Experimental.CausalEventTransport.Transport.comp_parent_injective
#print axioms PCRLean.Experimental.CausalBudgetCompiler.Step.noInfinitePath

end PCRLean.Experimental.U2EquivCausalIndex
