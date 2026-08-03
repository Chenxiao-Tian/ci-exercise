import PCRLean.Experimental.FaithfullyFlatCotangentFinitenessDescent
import PCRLean.Experimental.FaithfullyFlatGraphCentreDescent
import PCRLean.Experimental.PolynomialGraphCentreCotangentBasis
import PCRLean.Experimental.ReducedRegularGraphCentreCertificate

/-!
# Integrated faithfully flat conormal descent index

This index combines the current local graph-centre certificate with the exact
module-theoretic descent statement available without any scheme-level
shortcut:

* a polynomial graph centre has an explicit free conormal module;
* its actual ideal is proper and finitely generated;
* its quotient is reduced and regular under the corresponding base hypotheses;
* its ideal-power filtration reflects prime-power roots; and
* finiteness of a faithfully flat scalar extension of `I/I²` descends to the
  original conormal module.

The index does not assert projectivity or local freeness of the descended
conormal module.  Constructing the actual tensor-cotangent comparison for a
scheme-level fpqc graph atlas and descending finite projectivity remain open
geometric interfaces.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatConormalDescentKernelIndex

/-- Marker theorem confirming that the integrated dependency graph elaborates. -/
theorem loaded : True := True.intro

end FaithfullyFlatConormalDescentKernelIndex
end Experimental
end PCRLean
