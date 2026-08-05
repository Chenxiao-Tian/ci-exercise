import PCRLean.Experimental.PowerSaturationProduct
import PCRLean.Experimental.DivisorWordSaturation
import PCRLean.Experimental.SaturatedSourceCapsule
import PCRLean.Experimental.SaturationRecharge
import PCRLean.Experimental.DecalageSourceRank

/-!
# MLEL-X041 / SCD-DSW integrated experimental index

X041 proposes a factorization-independent **fully saturated** transform capsule
based on Cartier décalage.

At degree zero, successive exceptional-power saturations along a finite divisor
word equal one saturation by the product equation and are invariant under
permutation.  A finite exponent certificate records when the power-torsion
filtration has stabilized.  The corresponding quotient is the elementary
module shadow of a saturated `Lη` transform.

The fully saturated capsule need not equal an arbitrary iterated ordinary
strict transform: a later nonflat pullback can recharge torsion along an older
exceptional component.  `SaturationRecharge.lean` isolates the exact
module-level obstruction.  Equality with the actual word is therefore a
no-recharge theorem, not a consequence of saturation algebra alone.

The scheme-level candidate uses standard décalage facts:

* `η_f η_g = η_(f*g)` for Cartier equations;
* `Lη` commutes with flat base change, and after the canonical good-triple
  blowup it commutes with arbitrary pullback;
* on cohomology, `N` iterates quotient by `f^N`-torsion with the appropriate
  degree twist.

The exact Lean slice proves only submodule saturation laws, finite word
invariance, finite capsule bookkeeping, recharge clean/defect coverage, and
well-founded rank arithmetic.  It does not formalize derived décalage, actual
strict transforms, good-triple blowups, recharge vanishing/descent,
Rees--Serre flatification, regular centres, no-reset, termination, or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X041SaturatedDecalageIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X041SaturatedDecalageIndex
end Experimental
end PCRLean
