import PCRLean.Experimental.IntrinsicOrderIdealLinearEquiv
import PCRLean.Experimental.ProjectiveOrderIdealContent
import PCRLean.Experimental.MarkedClosureArrangement
import PCRLean.Experimental.CriticalPairTorExcess
import PCRLean.Experimental.SchurFittingComplexity

/-!
# MLEL-X033 / MAWS-TED integrated experimental index

This round refines D001 `G16/G20/G25` and corrects the geometric continuation
of `G11/G18`.

The retained proof architecture is:

```text
nonunique marked minimizers
-> canonical finite family of centre ideals
-> finite intersection semilattice C_(A union B)
-> same / disjoint / intersecting critical-pair split
-> Tor-independent clean chamber
-> layerwise wonderful ordinary-centre serialization
-> excess/nonclean chamber carried by a Fitting/Tor defect packet.
```

The source proves the intrinsic algebraic leaves:

* order ideals are invariant under linear equivalence;
* for a finite dual frame, the order ideal is the least content ideal
  absorbing the section;
* marked closure is monotone and pairwise intersection is `closure(A union B)`;
* active marked permissibility survives every such intersection closure;
* critical pairs admit exact same/disjoint/intersecting and
  Tor-independent/excess case splits;
* positive Schur pivots strictly lower finite presentation shape.

It does not prove that every minimizer arrangement is regular, clean,
passive-safe, boundary-SNC, or serializable by ordinary blowups.  Those are
explicit geometric edge obligations.  No general resolution theorem is
claimed.
-/

namespace PCRLean
namespace Experimental
namespace X033MinimizerArrangementIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X033MinimizerArrangementIndex
end Experimental
end PCRLean
