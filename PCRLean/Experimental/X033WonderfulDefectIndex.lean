import PCRLean.Experimental.IntrinsicOrderIdealLinearEquiv
import PCRLean.Experimental.ProjectiveOrderIdealContent
import PCRLean.Experimental.SymmetricConfigurationDifference
import PCRLean.Experimental.MarkedClosureArrangement
import PCRLean.Experimental.CanonicalIntersectionCompletion
import PCRLean.Experimental.CriticalPairTorExcess
import PCRLean.Experimental.TorCleanIntersectionBoundary
import PCRLean.Experimental.SchurFittingComplexity
import PCRLean.Experimental.CanonicalLayerScheduler
import PCRLean.Experimental.WonderfulProductIdeal
import PCRLean.Experimental.WonderfulLayerSerialization

/-!
# MLEL-X033 / MWB-DFI integrated experimental index

This round repairs the centre-serialization graph in two directions.

Positive clean chamber:

```text
finite minimizer family
-> canonical intersection completion
-> all scheme-theoretic intersections regular and jointly legal
-> maximal building set
-> canonical product ideal and minimal-layer schedule
-> symmetry-safe finite ordinary-centre word.
```

Defect chamber:

```text
common graph atlas
-> symmetric pairwise-difference contact packet
-> first nonregular or illegal intersection stratum
-> intrinsic Jacobian/Fitting/passive/boundary defect carrier
-> strict lower-support, Hasse-contact, or Schur-Fitting recursion.
```

Only the finite ideal/combinatorial interfaces, symmetric difference packet,
product invariant, and the conditional gate compiler are formalized here.  The
geometric maximal-building-set theorem and the comparison between product-ideal
blow-up and the iterated word are standard wonderful-model geometry;
construction and strict descent of the defect carrier remain open
load-bearing obligations.

The Tor predicate `I inf J = I * J` is retained only as a passive/derived
intersection diagnostic.  It is explicitly rejected as a complete
clean-intersection criterion.
-/

namespace PCRLean
namespace Experimental
namespace X033WonderfulDefectIndex

/-- Integrated source-elaboration marker. -/
theorem loaded : True := True.intro

end X033WonderfulDefectIndex
end Experimental
end PCRLean
