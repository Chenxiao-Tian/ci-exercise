import PCRLean.Experimental.PowerSaturationProduct
import PCRLean.Experimental.DivisorWordSaturation
import PCRLean.Experimental.SaturatedSourceCapsule
import PCRLean.Experimental.DecalageSourceRank

/-!
# MLEL-X041 / SCD-DSW integrated experimental index

X041 proposes a factorization-independent transform capsule based on saturated
Cartier décalage.

At degree zero, successive exceptional-power saturations along a finite divisor
word equal one saturation by the product equation and are invariant under
permutation.  A finite exponent certificate records when the power-torsion
filtration has stabilized.  The corresponding quotient is the elementary
module shadow of a saturated `Lη` transform.

The scheme-level candidate uses three standard facts:

* `η_f η_g = η_(f*g)` for Cartier equations;
* `Lη` commutes with flat base change, and after the canonical good-triple
  blowup it commutes with arbitrary pullback;
* on cohomology, one `Lη_f` layer removes the first `f`-torsion layer, so a
  finite iterate removes all exceptional power torsion of a coherent packet.

The exact Lean slice proves only the submodule saturation product law, finite
word invariance, finite capsule bookkeeping, and well-founded rank arithmetic.
It does not formalize derived décalage, good-triple blowups, strict transforms,
Rees--Serre flatification, source-word realization, regular centres, no-reset,
termination, or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X041SaturatedDecalageIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X041SaturatedDecalageIndex
end Experimental
end PCRLean
