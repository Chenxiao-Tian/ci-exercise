import PCRLean.Experimental.IntrinsicOrderIdealMinimality
import PCRLean.Experimental.SplitFreePresentationDualFrame
import PCRLean.Experimental.SplitCokernelOrderIdealCompiler

/-!
# X032 split-free order-ideal kernel index

This experimental index refines X031-G2 and D001 G11/FND-11.

It proves or packages the following exact edge chain:

* intrinsic order-ideal minimality and the unit-obstruction no-go require no
  frame and no projectivity assumption;
* a split finite-free presentation constructs a finite dual frame;
* conversely, a finite dual frame constructs a split finite-free presentation;
* compatible split presentations produce compatible dual frames and exact
  order-ideal base change;
* faithful flatness reflects zero, proper-nonzero, and unit branches; and
* a split finite-free presentation of a cokernel yields a frame-independent
  graph/hybrid/unit obstruction certificate.

The index does not construct the split cokernel presentation from an arbitrary
Hasse--Morita resolution state, does not construct a legal marked closure, and
does not prove general resolution.
-/

namespace PCRLean
namespace Experimental
namespace X032SplitFreeOrderIdealKernelIndex

/-- Marker theorem confirming elaboration of the integrated X032 dependency
slice. -/
theorem loaded : True := True.intro

end X032SplitFreeOrderIdealKernelIndex
end Experimental
end PCRLean
