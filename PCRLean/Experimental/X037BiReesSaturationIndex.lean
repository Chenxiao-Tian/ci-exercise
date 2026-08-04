import PCRLean.Experimental.ExceptionalLayerTransform
import PCRLean.Experimental.WeightedContactCleaning
import PCRLean.Experimental.FinitePrefixTailCriterion
import PCRLean.Experimental.SaturationDebtRank

/-!
# MLEL-X037 / BRT-ESD integrated experimental index

X037 corrects the naive ambient-flatification edge from X036.  Ordinary strict
transform on the carrier can remove all exceptional torsion at once, while one
ordinary ambient blowup generally removes only a positive controlled layer.
The tangent graph `x-u^m` exhibits the discrepancy:

```text
carrier strict transform of O/(u^m) = 0,
actual ambient projective-normal packet = O/(u^(m-1)).
```

The corrected candidate architecture is:

```text
finite Rees--Serre packet
-> flat strict-transform target on a carrier modification
-> bi-Rees saturation comparison
-> actual packet = flat target + exceptional-power discrepancy
-> finite exceptional-layer cleaning / weighted ambient domination
-> actual normal-flat packet
-> hereditary no-reset reentry.
```

The exact Lean leaves in this slice prove only:

* quotient-by-kernel equals the finite exceptional-layer image;
* weighted scalar contact factorization and strict debt drop;
* finite-prefix/eventual-tail coverage; and
* well-founded saturation/contact/passive/debt rank arithmetic.

They do not prove the scheme-level bi-Rees comparison, bounded coherent
saturation exponent, ordinary-centre realization of a weighted flatifier,
all-chart no-recharge, passive/logarithmic ambient legalization, termination,
or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X037BiReesSaturationIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X037BiReesSaturationIndex
end Experimental
end PCRLean
