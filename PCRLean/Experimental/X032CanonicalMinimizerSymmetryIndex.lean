import PCRLean.Experimental.CanonicalMarkedMinimizerSpace
import PCRLean.Experimental.TwoChoiceMarkedMinimizerNoGo

/-!
# MLEL-X032-B / CMS-NES integrated experimental index

The X031 minimal marked-closure compiler proves existence of a
cardinal-minimal acceptable subfamily.  This slice proves the sharp boundary:
minimality alone does not produce a canonical symmetry-compatible point.

Corrected interface:

* unique minimizer -> one canonical marked closure ideal;
* several minimizers -> retain the finite minimizer space/groupoid;
* ordinary resolution then requires a separate centre-word serialization edge
  with legality, critical-pair compatibility, no-reset, and strict macro rank.

This is an Experimental no-go/repair slice.  It does not prove that the
multi-minimizer groupoid always admits such a serialization.
-/

namespace PCRLean
namespace Experimental
namespace X032CanonicalMinimizerSymmetryIndex

theorem loaded : True := True.intro

end X032CanonicalMinimizerSymmetryIndex
end Experimental
end PCRLean
