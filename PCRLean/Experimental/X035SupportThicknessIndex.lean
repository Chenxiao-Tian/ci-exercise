import PCRLean.Experimental.FiniteBadStratumCoverage
import PCRLean.Experimental.SupportThicknessAlternative
import PCRLean.Experimental.StratumInductionActiveLift
import PCRLean.Experimental.SupportThicknessRank
import PCRLean.Experimental.NilpotentThickness

/-!
# MLEL-X035 / STD-ALI integrated experimental index

The X034 first-defect branch is refined as follows.

```text
finite intersection arrangement
-> full finite bad-stratum layer, without choosing one point
-> support-singular sublayer
     lower-dimensional relative resolution
     + ambient lifting of the same ordinary centres
-> regular-support thickness sublayer
     nilpotent normal-cone / contact / Hasse / Fitting packet
     + strict thickness descent
-> clean arrangement
-> wonderful ordinary serialization.
```

The exact Lean leaves in this slice prove only:

* finite choice-free clean/defect coverage;
* disjoint exhaustive support-singular/thickness partition;
* active marked legality under ambient lifting of centres carried by a stratum;
* well-founded support/thickness arithmetic; and
* elementary nilpotent-thickness certificates.

They do not prove lower-dimensional relative resolution, passive or SNC
ambient lifting, strict transformation of the thickness packet, wonderful
serialization, global termination, or general positive-characteristic
resolution.
-/

namespace PCRLean
namespace Experimental
namespace X035SupportThicknessIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X035SupportThicknessIndex
end Experimental
end PCRLean
