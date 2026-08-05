import PCRLean.Experimental.HomogenizedGradedFlatness
import PCRLean.Experimental.DegreewiseFlagFlatLiftCompiler
import PCRLean.Experimental.SourceWordCofinalityCompiler
import PCRLean.Experimental.HomogenizedCarrierRank

/-!
# MLEL-X041 / HNC-STC-RFL integrated experimental index

The X041 candidate makes two critical compressions.

```text
complete affine normal-cone graded module
-> canonical homogenization on P(O ⊕ I/I²)
-> proper coherent packet retaining every normal degree
-> functorial flatification under flat base change;

centre-exact source words
-> strict-transform transitivity
-> finite common product refinement
-> flat terminal transforms pull back through the refinement.
```

The remaining project-specific edge is the all-chart Regular-Flag Flat-Lift:
a nested jointly legal centre must produce degreewise Cartier-twisted
isomorphisms between old and new normal graded pieces.  Once these
isomorphisms exist, the Lean backend in this slice compiles flatness of every
new piece, the full associated graded module, and its homogenized completion.

The exact Lean leaves prove only:

* flatness equivalence for the triangular homogenized direct-sum module;
* degreewise-equivalence transport of normal flatness;
* finite source-portfolio flatness under certified common-refinement
  equivalences; and
* well-founded carrier/source/flag/word rank arithmetic.

They do not construct symmetric algebras, projective bundles, coherent
homogenization, Rydh flatifiers, centre-exact composite blowup ideals, strict-
transform transitivity in schemes, Regular-Flag Flat-Lift, no-reset,
termination, or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X041HomogenizedNormalCofinalityIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X041HomogenizedNormalCofinalityIndex
end Experimental
end PCRLean
