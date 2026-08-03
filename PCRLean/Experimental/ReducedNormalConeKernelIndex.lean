import PCRLean.Experimental.FrobeniusSupportReduced
import PCRLean.Experimental.ReducedCoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity
import PCRLean.Experimental.ReducedGraphCentreQuotient
import PCRLean.Experimental.CoordinateCentreCotangentBasis
import PCRLean.Experimental.PolynomialGraphCentreCotangentBasis
import PCRLean.Experimental.ReducedFrobeniusNormalLocalModel
import PCRLean.Experimental.ReducedNormalConePowerModel

/-!
# Integrated reduced normal-cone kernel index

This index forces one dependency graph through the new reduced-coefficient
heredity layer:

* prime-power support scaling over arbitrary reduced coefficient rings;
* exact coordinate-centre reflection;
* necessity of reducedness for coordinate centres;
* exact polynomial graph-centre reflection;
* necessity of reducedness for graph centres;
* the exact graph evaluation kernel and quotient certificate;
* reducedness and regularity of graph-centre quotients;
* explicit free bases of coordinate and polynomial graph conormal modules
  `I/I²`;
* faithfully flat descent from reduced coordinate and graph local models; and
* an abstract reduced normal-cone power model compiling layer embeddings into
  full Frobenius-normality.

The index is experimental. It does not assert existence of the required
scheme-level graph atlas or associated-graded model and does not prove
resolution.
-/

namespace PCRLean
namespace Experimental
namespace ReducedNormalConeKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end ReducedNormalConeKernelIndex
end Experimental
end PCRLean
