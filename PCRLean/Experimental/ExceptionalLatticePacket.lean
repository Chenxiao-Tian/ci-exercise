import Mathlib
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Two-sided exceptional lattice packets

After exceptional torsion is removed, the actual ambient packet and the flat
strict-transform target need not be equal lattices inside their common
localization.  A uniform scalar saturation exponent is therefore not the full
invariant.  The canonical finite packet is the intersection/sum diagram

```text
actual ∩ target  -> actual, target -> actual + target.
```

Noether's second isomorphism theorem identifies the two quotient descriptions
of each side of the discrepancy.  The resulting exceptional quotients are the
objects to be filtered by powers of the exceptional ideal and processed by
Fitting/Schur elementary transforms.

This file proves only the exact submodule algebra.  It does not construct the
common localization, prove exceptional-power torsion, or realize an elementary
lattice transform by an ambient blowup.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalLatticePacket

noncomputable section

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Two coherent lattices represented abstractly as submodules of one common
ambient module. -/
structure Packet where
  actual : Submodule R M
  target : Submodule R M

namespace Packet

/-- The common lower lattice. -/
def lower (P : Packet (R := R) (M := M)) : Submodule R M :=
  P.actual ⊓ P.target

/-- The common upper lattice. -/
def upper (P : Packet (R := R) (M := M)) : Submodule R M :=
  P.actual ⊔ P.target

/-- Actual modulo the common lower lattice equals the contribution of the
actual lattice to the common upper quotient. -/
noncomputable def actualDefectEquiv
    (P : Packet (R := R) (M := M)) :=
  Submodule.quotientInfEquivSupQuotient P.actual P.target

/-- Target modulo the common lower lattice equals the contribution of the
target lattice to the common upper quotient. -/
noncomputable def targetDefectEquiv
    (P : Packet (R := R) (M := M)) :=
  Submodule.quotientInfEquivSupQuotient P.target P.actual

/-- The lower lattice lies in the actual lattice. -/
theorem lower_le_actual (P : Packet (R := R) (M := M)) :
    P.lower ≤ P.actual :=
  inf_le_left

/-- The lower lattice lies in the target lattice. -/
theorem lower_le_target (P : Packet (R := R) (M := M)) :
    P.lower ≤ P.target :=
  inf_le_right

/-- The actual lattice lies in the common upper lattice. -/
theorem actual_le_upper (P : Packet (R := R) (M := M)) :
    P.actual ≤ P.upper :=
  le_sup_left

/-- The target lattice lies in the common upper lattice. -/
theorem target_le_upper (P : Packet (R := R) (M := M)) :
    P.target ≤ P.upper :=
  le_sup_right

/-- Equality of the two lattices collapses both bounds. -/
theorem lower_eq_upper_of_eq
    (P : Packet (R := R) (M := M))
    (h : P.actual = P.target) :
    P.lower = P.upper := by
  simp [lower, upper, h]

end Packet

end

end ExceptionalLatticePacket
end Experimental
end PCRLean
