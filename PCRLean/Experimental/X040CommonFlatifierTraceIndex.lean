import PCRLean.Experimental.MinimalStratumNesting
import PCRLean.Experimental.CommonTraceProduct
import PCRLean.Experimental.CommonFlatifierBudgetRank
import PCRLean.Experimental.FiniteArrangementCompletion
import PCRLean.Experimental.CrossCarrierCompletionModel

/-!
# MLEL-X040 / CFT-ACN integrated experimental index

X040 corrects independent maximal-carrier preparation.  Preparatory flatifier
centres attached to different carriers may cross.  The candidate replacement
aggregates all source-labelled ambient trace ideals into one finite product,
closes the resulting source arrangement under intersections, resolves every
bad intersection in lower support dimension, and serializes the clean
completion deepest first.

The standard blowup of a finite product ideal is a common refinement of the
source blowups.  A regular word principalizing the common product therefore
factors through every source flatifier.  The scheme-level factorization,
source-pure-transform comparison, supported principalization, and regular-flag
transport are not proved in this file.

The exact Lean leaves certify only:

* finite intersection-completion search space;
* the crossing-source no-go model;
* minimal-stratum disjoint-or-contained coverage;
* elementary binary trace-product containments and symmetry; and
* well-founded common-support/source/word rank arithmetic.
-/

namespace PCRLean
namespace Experimental
namespace X040CommonFlatifierTraceIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X040CommonFlatifierTraceIndex
end Experimental
end PCRLean
