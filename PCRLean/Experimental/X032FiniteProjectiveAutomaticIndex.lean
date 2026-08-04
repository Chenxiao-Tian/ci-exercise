import PCRLean.Experimental.FiniteProjectiveAutomaticDualFrame
import PCRLean.Experimental.FiniteProjectiveCokernelOrderIdealCompiler

/-!
# MLEL-X032D / FPA-IOM integrated experimental index

This slice closes the purely algebraic input-reduction edge of D001
`G11 / FND-11`:

```text
finite projective module
-> finite generating family
-> surjective finite-free presentation
-> projective splitting
-> finite dual frame
-> intrinsic cokernel order-ideal trichotomy.
```

Thus a finite dual frame is not independent data once finiteness and
projectivity are available.  The remaining load-bearing edge is geometric:
construct the relevant finite-projective cokernel functorially from every
resolution state and transport the resulting presentations/status packages on
all Fitting charts and overlaps.

No declaration in this file proves a regular blowup centre or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X032FiniteProjectiveAutomaticIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X032FiniteProjectiveAutomaticIndex
end Experimental
end PCRLean
