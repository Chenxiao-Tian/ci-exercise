import PCRLean.Experimental.PowerSaturation
import PCRLean.Experimental.CommonCoreInterchange
import PCRLean.Experimental.BigradedFlatnessCompiler
import PCRLean.Experimental.FlatKillLegalizationRank

/-!
# MLEL-X038 / TVC-FKL integrated experimental index

X038 replaces one speculative bifiltered comparison map by a two-surjection
common-core diagram.  On an affine blowup chart, the right kernel records
nonexact base change of a filtration, while the left kernel records exceptional
power saturation of the transformed filtration.  The latter is a relative
Valabrega-type defect.

```text
old graded piece after chart pullback -->> common image-filtration core
new normal graded piece with Cartier twist -->> common image-filtration core
```

When both kernels vanish, the common-core compiler gives a canonical linear
equivalence.  The geometric proposal packages the two coherent kernels with
the complete associated-graded passive portfolio and kills them by a
lower-dimensional, centre-enriched flatification/legalization macro.

The affine normal-cone correction treats the whole graded or bigraded packet as
one direct-sum module over the carrier.  No projective tail is needed for the
module-theoretic flatness compiler.

The exact Lean leaves in this slice prove only:

* elementary relative power saturation and quotient-power-torsion identities;
* regular exceptional parameters create no power torsion or new saturation;
* the abstract two-surjection common-core equivalence compiler;
* flatness equivalences for complete bigraded packets and finite portfolios;
* well-founded arithmetic for the dimension/defect/contact/debt rank.

They do not construct blowup charts, image filtrations, mixed Rees algebras,
finite Tor--Valabrega defect sheaves, flatification words, ambient trace
centres, hereditary reentry, termination, or general positive-characteristic
resolution.
-/

namespace PCRLean
namespace Experimental
namespace X038TorValabregaCommonCoreIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X038TorValabregaCommonCoreIndex
end Experimental
end PCRLean
