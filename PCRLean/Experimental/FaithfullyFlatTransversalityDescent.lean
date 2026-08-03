import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.BoundaryTransversalityGate
import PCRLean.Experimental.FaithfullyFlatMarkedCentreDescent

/-!
# Faithfully flat descent of ideal-theoretic transversality

Let `A → B` be faithfully flat.  Suppose extension preserves the relevant
intersection,

`map(I ⊓ J) = map(I) ⊓ map(J)`.

If the extended ideals are transverse, then the original ideals are transverse.
The proof uses only:

* injectivity of ideal extension under faithful flatness;
* preservation of ideal products by every ring homomorphism; and
* the stated intersection comparison.

Thus the remaining passive/Tor obligation is exposed exactly: prove the
intersection comparison for the chosen centre and boundary ideals.  No appeal
to an unspecified flatness argument is hidden inside the conclusion.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatTransversalityDescent

noncomputable section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

open BoundaryTransversalityGate
open FaithfullyFlatMarkedCentreDescent

/-- Transversality descends once extension preserves the relevant
intersection. -/
theorem transverse_of_map
    (I J : Ideal A)
    (hInf : (I ⊓ J).map (algebraMap A B) =
      I.map (algebraMap A B) ⊓ J.map (algebraMap A B))
    (hTrans : Transverse
      (I.map (algebraMap A B))
      (J.map (algebraMap A B))) :
    Transverse I J := by
  unfold Transverse at hTrans ⊢
  apply eq_of_map_eq_map (B := B)
  rw [hInf, Ideal.map_mul]
  exact hTrans

/-- Equivalent version with the intersection comparison oriented in the other
direction. -/
theorem transverse_of_map'
    (I J : Ideal A)
    (hInf : I.map (algebraMap A B) ⊓ J.map (algebraMap A B) =
      (I ⊓ J).map (algebraMap A B))
    (hTrans : Transverse
      (I.map (algebraMap A B))
      (J.map (algebraMap A B))) :
    Transverse I J :=
  transverse_of_map (B := B) I J hInf.symm hTrans

end

end FaithfullyFlatTransversalityDescent
end Experimental
end PCRLean
