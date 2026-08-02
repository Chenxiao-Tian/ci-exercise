import Mathlib
import PCRLean.MultiHasseOnlyDescent
import PCRLean.FrobeniusRootCentre

/-!
# Multi-owner Frobenius cores on a realized finite product frame

A finite family of Hasse-stable owner ideals descends owner by owner.  Taking
the finite supremum of the contracted cores therefore produces one base ideal
whose extension contains every active owner.  This is the exact algebraic
multi-owner input required by the coordinate realization chamber of MLEL-002.
-/

namespace PCRLean
namespace MultiOwnerHasseCore

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {ω : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ω] [DecidableEq ω]
variable {spec : List (Nat × R)}

/-- Finite supremum of the contracted owner cores. -/
def jointCore
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (owners : ω → Ideal A) : Ideal R :=
  Finset.univ.sup (fun i => F.core (owners i))

/-- Finite supremum of the active owner ideals. -/
def jointOwnerIdeal (owners : ω → Ideal A) : Ideal A :=
  Finset.univ.sup owners

/-- A Hasse-stable owner is already its own saturation and hence descends
exactly from its contraction. -/
theorem owner_eq_coreExtension_of_stable
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
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

/-- Every individual core is contained in the finite joint core. -/
theorem core_le_jointCore
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (owners : ω → Ideal A) (i : ω) :
    F.core (owners i) ≤ jointCore F owners := by
  exact Finset.le_sup
    (f := fun j => F.core (owners j)) (Finset.mem_univ i)

/-- Every stable owner is contained in the extension of the joint core. -/
theorem owner_le_jointCoreExtension
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (i : ω) :
    owners i ≤ (jointCore F owners).map (algebraMap R A) := by
  rw [owner_eq_coreExtension_of_stable F (owners i) (hstable i)]
  exact Ideal.map_mono (core_le_jointCore F owners i)

/-- The whole finite active union is controlled by the joint core extension. -/
theorem jointOwnerIdeal_le_jointCoreExtension
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i)) :
    jointOwnerIdeal owners ≤
      (jointCore F owners).map (algebraMap R A) := by
  rw [jointOwnerIdeal]
  exact Finset.sup_le fun i hi =>
    owner_le_jointCoreExtension F owners hstable i

/-- Any root section for the joint core gives one actual root ideal permissible
for every owner. -/
theorem every_owner_permissible
    {q : Nat} (hq : 0 < q)
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i))
    (i : ω) :
    MarkedIdeal.Permissible
      (R := A) ⟨owners i, q, hq⟩
      (S.rootIdeal (jointCore F owners)) := by
  exact S.markedPacket_permissible hq
    (owner_le_jointCoreExtension F owners hstable i)

/-- The finite joint owner ideal is permissible for the same actual root ideal. -/
theorem jointOwnerIdeal_permissible
    {q : Nat} (hq : 0 < q)
    (F : MultiHasseOnlyDescent.RealizedFrame
      (R := R) (A := A) spec)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ω → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable F.hasseAddHom (owners i)) :
    MarkedIdeal.Permissible
      (R := A) ⟨jointOwnerIdeal owners, q, hq⟩
      (S.rootIdeal (jointCore F owners)) := by
  exact S.markedPacket_permissible hq
    (jointOwnerIdeal_le_jointCoreExtension F owners hstable)

end

end MultiOwnerHasseCore
end PCRLean
