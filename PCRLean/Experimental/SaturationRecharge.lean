import Mathlib
import PCRLean.Experimental.PowerSaturationProduct
import PCRLean.Experimental.DivisorWordSaturation

/-!
# Exceptional saturation recharge

Successive ordinary strict transforms remove torsion along the exceptional
divisor created at each step.  A later nonflat pullback can in principle create
new torsion along an older exceptional component.  The total-divisor saturated
transform removes this new torsion as well.

The difference between the inherited submodule and its full divisor-word
saturation is the **recharge defect**.  The actual iterated transform agrees
with the factorization-independent saturated capsule only after this defect
vanishes.  Thus saturated décalage does not replace the no-recharge theorem; it
isolates its exact finite obstruction.

This file proves only the elementary module-level clean/defect coverage and the
word/product equivalence.  It does not construct strict transforms, recharge
modules on schemes, or hereditary no-reset.
-/

namespace PCRLean
namespace Experimental
namespace SaturationRecharge

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open PowerSaturationProduct DivisorWordSaturation

/-- No new exceptional power torsion is present after the inherited quotient. -/
def RechargeFree (q : R) (N : Submodule R M) : Prop :=
  powerSaturation q N = N

/-- A witness to exceptional recharge. -/
def RechargeWitness (q : R) (N : Submodule R M) :=
  {x : M // x ∈ powerSaturation q N ∧ x ∉ N}

/-- Recharge-free data has no recharge witness. -/
theorem no_witness_of_rechargeFree
    {q : R} {N : Submodule R M}
    (h : RechargeFree q N) :
    ¬ Nonempty (RechargeWitness q N) := by
  rintro ⟨x⟩
  exact x.property.2 (by simpa [RechargeFree, h] using x.property.1)

/-- If saturation strictly enlarges the inherited submodule, there is a
concrete recharge witness. -/
theorem exists_witness_of_not_rechargeFree
    {q : R} {N : Submodule R M}
    (h : ¬ RechargeFree q N) :
    Nonempty (RechargeWitness q N) := by
  classical
  have hne : powerSaturation q N ≠ N := h
  have hnotle : ¬ powerSaturation q N ≤ N := by
    intro hle
    exact hne (le_antisymm hle (le_powerSaturation q N))
  push_neg at hnotle
  obtain ⟨x, hxsat, hxN⟩ := hnotle
  exact ⟨⟨x, hxsat, hxN⟩⟩

/-- Exact clean/defect equivalence. -/
theorem witness_nonempty_iff_not_rechargeFree
    (q : R) (N : Submodule R M) :
    Nonempty (RechargeWitness q N) ↔ ¬ RechargeFree q N := by
  constructor
  · intro hw hfree
    exact no_witness_of_rechargeFree hfree hw
  · exact exists_witness_of_not_rechargeFree

/-- No recharge for a finite divisor word is the same as no recharge for its
product equation. -/
theorem word_rechargeFree_iff
    (qs : List R) (N : Submodule R M) :
    wordSaturation qs N = N ↔ RechargeFree qs.prod N := by
  rw [wordSaturation_eq_prod]
  rfl

/-- Recharge freedom is invariant under permutation of a divisor word. -/
theorem word_rechargeFree_iff_of_perm
    {qs rs : List R} (hperm : qs.Perm rs) (N : Submodule R M) :
    (wordSaturation qs N = N) ↔ (wordSaturation rs N = N) := by
  rw [wordSaturation_eq_of_perm hperm N]

/-- The choice-free status of a total exceptional divisor capsule. -/
inductive Status (q : R) (N : Submodule R M) : Type (max u v) where
  | clean (rechargeFree : RechargeFree q N)
  | defect (witness : Nonempty (RechargeWitness q N))

/-- Every capsule lies in the no-recharge or recharge chamber. -/
noncomputable def classify (q : R) (N : Submodule R M) : Status q N := by
  classical
  by_cases h : RechargeFree q N
  · exact Status.clean h
  · exact Status.defect (exists_witness_of_not_rechargeFree h)

end

end SaturationRecharge
end Experimental
end PCRLean
