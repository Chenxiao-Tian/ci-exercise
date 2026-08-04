import PCRLean.Experimental.PowerSaturation
import PCRLean.Experimental.ControlledCoreInterchange
import PCRLean.Experimental.BigradedFlatnessCompiler
import PCRLean.Experimental.FlatKillLegalizationRank

/-!
# MLEL-X038 / TVF-ANC integrated experimental index

The final X038 candidate replaces both the X037 direct interchange map and the
first X038 two-epimorphism cospan by a controlled-core factorization:

```text
old controlled graded object
  -- Tor/base-change epimorphism -->
controlled-transform core
  -- Valabrega saturation map -->
new strict-carrier normal graded object.
```

The first map has a kernel.  The second map can have both kernel and cokernel;
the example `J=(q*y) subset L=(y)` shows that it need not be surjective before
saturation compatibility is proved.

The affine normal-cone correction treats the complete associated-graded and
mixed-Rees packets as finite direct-sum modules over the carrier.  No
projective tail is needed for the module-theoretic flatness compiler.

The exact Lean leaves in this slice prove only:

* elementary relative power saturation and quotient-power-torsion identities;
* regular exceptional parameters create no power torsion or new saturation;
* the abstract Tor-kernel/Valabrega-kernel-and-cokernel factorization compiler;
* flatness equivalences for complete bigraded packets and finite portfolios;
* well-founded arithmetic for the dimension/defect/contact/debt rank.

They do not construct blowup charts, controlled ideals, mixed Rees algebras,
finite transform-defect sheaves, flatification words, ambient trace centres,
hereditary reentry, termination, or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X038TorValabregaCommonCoreIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X038TorValabregaCommonCoreIndex
end Experimental
end PCRLean
