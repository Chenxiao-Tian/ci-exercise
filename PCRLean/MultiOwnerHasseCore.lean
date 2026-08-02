import Mathlib
import PCRLean.MultiHasseOnlyDescent
import PCRLean.FrobeniusRootCentre

/-!
# Multi-owner exact Frobenius cores

For a realized finite-product Frobenius frame, Hasse-stable owner ideals descend
individually. Since ideal extension preserves arbitrary suprema, their joint
active ideal is exactly the extension of the supremum of their contracted cores.
-/

namespace PCRLean
namespace MultiOwnerHasseCore

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {ω : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable {spec : List (Nat × R)}

abbrev Frame := MultiHasseOnlyDescent.RealizedFrame

/-- Supremum of all contracted owner cores. -/
def jointCore
    (F : Frame (R := R) (A := A) spec)
    (owners : ω → Ideal A) : Ideal R :=
  ⨆ i, F.core (owners i)

/-- Supremum of all active owner ideals. -/
def jointOwnerIdeal (owners : ω → Ideal A) : Ideal A :=
  ⨆ i, owners i

/-- A Hasse-stable owner is already its own saturation and therefore descends
exactly from its contracted core. -/
theorem owner_eq_coreExtension_of_stable
    (F : Frame (R := R) (A := A) spec)
    (I : Ideal A)
    (hstable : DifferentialIdealSaturation.Stable F.hasseAddHom I) :
    I = (F.core I).map (algebraMap R A) := by
  have hfix : F.hasseSaturation I = I :=
    DifferentialIdealSaturation.saturation_eq_self_of_stable
      F.hasseAddHom I hstable
  calc
    I = F.hasseSaturation I := hfix.symm
    _ = (F.core I).map (algebraMap R A) :=
      F.hasseSaturation_eq_map_core I

/-- Every owner is contained in the extension of the joint core. -/
theorem owner_le_jointCoreExtension
    (F : Frame (R := R) (A := A) spec)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (i : ω) :
    owners i ≤ (jointCore F owners).map (algebraMap R A) := by
  rw [owner_eq_coreExtension_of_stable F (owners i) (hstable i)]
  exact Ideal.map_mono (le_iSup (fun j => F.core (owners j)) i)

/-- Exact joint descent: joining owners before or after Frobenius contraction
produces the same ideal. -/
theorem jointOwnerIdeal_eq_map_jointCore
    (F : Frame (R := R) (A := A) spec)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i)) :
    jointOwnerIdeal owners =
      (jointCore F owners).map (algebraMap R A) := by
  calc
    jointOwnerIdeal owners =
        ⨆ i, (F.core (owners i)).map (algebraMap R A) := by
      apply iSup_congr
      intro i
      exact owner_eq_coreExtension_of_stable F (owners i) (hstable i)
    _ = (jointCore F owners).map (algebraMap R A) := by
      simpa [jointCore] using
        (Ideal.map_iSup (algebraMap R A)
          (fun i => F.core (owners i))).symm

/-- A root section makes the same actual root ideal permissible for every owner. -/
theorem every_owner_permissible
    {q : Nat} (hq : 0 < q)
    (F : Frame (R := R) (A := A) spec)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A) ⟨owners i, q, hq⟩ (S.rootIdeal (jointCore F owners)) := by
  exact S.markedPacket_permissible hq
    (owner_le_jointCoreExtension F owners hstable i)

/-- The whole joint owner ideal is permissible for the same root centre. -/
theorem jointOwnerIdeal_permissible
    {q : Nat} (hq : 0 < q)
    (F : Frame (R := R) (A := A) spec)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i)) :
    MarkedIdeal.Permissible
      (R := A) ⟨jointOwnerIdeal owners, q, hq⟩
      (S.rootIdeal (jointCore F owners)) := by
  exact S.markedPacket_permissible_of_eq hq
    (jointOwnerIdeal_eq_map_jointCore F owners hstable)

end

end MultiOwnerHasseCore
end PCRLean
