import PCRLean.Experimental.CentreEnrichedPureTransform
import PCRLean.Experimental.BifilteredLegalizationRank
import PCRLean.Experimental.FinitePrefixTailCriterion

/-!
# MLEL-X037 / CTW-BRT integrated experimental index

X037 corrects a morphism-only ambiguity in the X036 ambient-legalization
proposal.  Strict and pure transforms remember the chosen blowup centre, even
when the induced carrier blowup is the identity because the centre is Cartier
on the carrier.  The candidate replacement records centre-enriched
Cartier-trace words and seeks one bifiltered Rees object controlling both
projective-normal passive flatification and anchor-contact cleaning.

The exact Lean leaves in this slice prove only:

* forgetting the centre/pure-transform payload is not injective on a nontrivial
  module;
* finite-prefix plus eventual-tail coverage for a degreewise condition; and
* well-founded arithmetic for the commutator/passive/contact/debt rank.

They do not prove a bigraded Rees comparison, ambient Cartier-trace lift,
projective-normal flatification, contact transform, all-chart reentry,
termination, or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X037CartierTraceReesTransportIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X037CartierTraceReesTransportIndex
end Experimental
end PCRLean
