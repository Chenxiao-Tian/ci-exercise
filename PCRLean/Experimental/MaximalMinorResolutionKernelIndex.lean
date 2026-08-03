import PCRLean.Experimental.FittingMinorFaithfulCover
import PCRLean.Experimental.AugmentedMinorRangeNecessity
import PCRLean.Experimental.MaximalMinorRangeCriterion
import PCRLean.Experimental.MaximalMinorGlobalResolutionMacro
import PCRLean.Experimental.MaximalMinorPresentationIndependence
import PCRLean.Experimental.PolynomialGraphSupportEquality
import PCRLean.Experimental.PolynomialGraphActionBoundary

/-!
# Focused maximal-minor resolution index

This index isolates the new determinantal bridge of the current round:

* finite Fitting covers jointly reflect equality;
* every actual solution forces augmented-minor vanishing;
* full maximal-minor cover plus augmented-minor vanishing is equivalent to
  unique solvability;
* the resulting actual global graph and resolution macro are independent of
  the chosen equation presentation;
* the pure graph-root packet has exactly the graph support; and
* the one-normal-variable Cartier boundary is separated from higher-rank
  ordinary-centre candidates.

The index is experimental and does not assert general resolution.
-/

namespace PCRLean
namespace Experimental
namespace MaximalMinorResolutionKernelIndex

/-- Marker theorem confirming elaboration of the focused dependency graph. -/
theorem loaded : True := True.intro

end MaximalMinorResolutionKernelIndex
end Experimental
end PCRLean
