import PCRLean.Experimental.FiniteProjectivePresentationDualFrame
import PCRLean.Experimental.FiniteProjectiveOrderIdealCompiler
import PCRLean.Experimental.SplitCokernelOrderIdealCompiler

/-!
# MLEL-X032C / FPP-DF integrated experimental index

This slice refines D001 `G11 / FND-11` and X031-G2.

Positive edge:

```text
projective cokernel
+ surjective finite-free presentation
-> linear splitting
-> explicit finite dual frame
-> intrinsic order-ideal graph/proper-hybrid/unit compiler
```

The frame is no longer an independent input. Compatible split presentations
also yield the existing exact base-change interface and faithful-flat
reflection of the proper-nonzero branch.

The remaining algebraic edge is construction of the finite-free presentation
from finite generation. The remaining geometric edges are construction of the
finite-projective cokernel from an arbitrary resolution state, compatible
presentation transport on a finite Fitting atlas, and regular/legal
actualization of the proper-nonzero closure.

This file is Experimental and does not prove general resolution.
-/

namespace PCRLean
namespace Experimental
namespace X032FiniteProjectivePresentationIndex

/-- Marker theorem confirming elaboration of the integrated dependency slice. -/
theorem loaded : True := True.intro

end X032FiniteProjectivePresentationIndex
end Experimental
end PCRLean
