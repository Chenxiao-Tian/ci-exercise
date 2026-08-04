import Mathlib

/-!
# Active marked legality under stratum-induction lifts

Suppose an active owner ideal `D` is marked-permissible for an intersection
stratum ideal `Z`, so `D ≤ Z^m`.  Every ordinary centre lying inside that
stratum has a larger defining ideal `C`, with `Z ≤ C`.  Ideal-power
monotonicity therefore gives `D ≤ C^m`.

This is the exact algebraic reason that a lower-dimensional centre word carried
by a bad intersection stratum can be lifted to the ambient scheme without
losing active marked permissibility.  Passive Tor safety, normal flatness,
boundary SNC, regularity of the ambient lift, strict-transform compatibility,
and strict geometric descent remain separate geometric obligations.
-/

namespace PCRLean
namespace Experimental
namespace StratumInductionActiveLift

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Marked permissibility of an owner ideal for a centre ideal. -/
def MarkedPermissible (D C : Ideal R) (m : ℕ) : Prop :=
  D ≤ C ^ m

/-- Enlarging the centre ideal preserves active marked permissibility. -/
theorem markedPermissible_mono
    {D Z C : Ideal R} {m : ℕ}
    (hDZ : MarkedPermissible D Z m)
    (hZC : Z ≤ C) :
    MarkedPermissible D C m := by
  exact hDZ.trans (pow_le_pow_left' hZC m)

/-- One ordinary centre lying inside a fixed stratum.  Scheme-theoretically,
`Z ≤ C` means `V(C) ⊆ V(Z)`. -/
structure RelativeCentre (Z : Ideal R) where
  ideal : Ideal R
  stratum_le : Z ≤ ideal

/-- A finite lower-dimensional centre word carried by one stratum. -/
abbrev RelativeWord (Z : Ideal R) := List (RelativeCentre Z)

/-- Every relative centre inherits every active marked certificate held by the
carrier stratum. -/
theorem relativeCentre_active
    {D Z : Ideal R} {m : ℕ}
    (hDZ : MarkedPermissible D Z m)
    (C : RelativeCentre Z) :
    MarkedPermissible D C.ideal m :=
  markedPermissible_mono hDZ C.stratum_le

/-- Pointwise active legality of an entire relative centre word. -/
theorem relativeWord_active
    {D Z : Ideal R} {m : ℕ}
    (hDZ : MarkedPermissible D Z m)
    (W : RelativeWord Z) :
    ∀ C ∈ W, MarkedPermissible D C.ideal m := by
  intro C hC
  exact relativeCentre_active hDZ C

/-- The active certificate is independent of which occurrence of a centre is
chosen in the word.  Membership is retained in the statement because the
geometric compiler consumes a finite word rather than an arbitrary centre. -/
theorem active_of_mem_relativeWord
    {D Z : Ideal R} {m : ℕ}
    (hDZ : MarkedPermissible D Z m)
    {W : RelativeWord Z} {C : RelativeCentre Z}
    (hC : C ∈ W) :
    MarkedPermissible D C.ideal m := by
  exact relativeWord_active hDZ W C hC

end

end StratumInductionActiveLift
end Experimental
end PCRLean
