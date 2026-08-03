import PCRLean.Experimental.FrobeniusSupportReduced
import PCRLean.Experimental.ReducedCoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity
import PCRLean.Experimental.ReducedFrobeniusNormalLocalModel

/-!
# Integrated reduced normal-cone kernel index

This index forces one dependency graph through the new reduced-coefficient
heredity layer:

* prime-power support scaling over arbitrary reduced coefficient rings;
* exact coordinate-centre reflection;
* necessity of reducedness for coordinate centres;
* exact polynomial graph-centre reflection;
* necessity of reducedness for graph centres; and
* faithfully flat descent from reduced coordinate and graph local models.

The index is experimental.  It does not assert existence of the required
scheme-level graph atlas and does not prove resolution.
-/

namespace PCRLean
namespace Experimental
namespace ReducedNormalConeKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end ReducedNormalConeKernelIndex
end Experimental
end PCRLean
