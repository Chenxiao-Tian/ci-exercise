import Mathlib
import PCRLean.HasseGrowthDescentDichotomy
import PCRLean.FrobeniusRootCentre
import PCRLean.SplitFrobeniusRootCentre
import PCRLean.OwnerJoint

/-!
# Joint active-owner Frobenius centres

A resolution centre must be legal for every active owner, not only for one
chosen equation.  On a common monogenic Frobenius frame, stable owner ideals
descend to base ideals.  Their finite supremum is the joint Frobenius core.
Every owner is contained in the extension of that joint core, so the actual
root ideal of the joint core is marked-permissible for all owners at once.

The joint core may be the unit ideal; this is an explicit owner-conflict
certificate rather than a hidden failure.  If a split root section is available
and the joint core is proper, the common root centre is also proper.
-/

namespace PCRLean
namespace JointFrobeniusOwnerCentre

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {ι : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]
variable {q : Nat} {t : R}

abbrev Frame := MonogenicFrobeniusFrame.Frame

/-- Finite supremum of all descended owner cores. -/
def jointCore
    (F : Frame (R := R) (A := A) q t)
    (owners : ι → Ideal A) : Ideal R :=
  Finset.univ.sup
    (fun i => HasseSaturationDescent.frobeniusCore F (owners i))

/-- Every individual owner core is contained in the joint core. -/
theorem core_le_jointCore
    (F : Frame (R := R) (A := A) q t)
    (owners : ι → Ideal A) (i : ι) :
    HasseSaturationDescent.frobeniusCore F (owners i) ≤
      jointCore F owners := by
  exact Finset.le_sup (f := fun j =>
    HasseSaturationDescent.frobeniusCore F (owners j))
    (Finset.mem_univ i)

/-- A stable owner is contained in the extension of the joint core. -/
theorem owner_le_jointCoreExtension
    (F : Frame (R := R) (A := A) q t)
    (owners : ι → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable
        (HasseSaturationDescent.transportedHasseAddHom F) (owners i))
    (i : ι) :
    owners i ≤ (jointCore F owners).map (algebraMap R A) := by
  rw [HasseGrowthDescentDichotomy.eq_coreExtension_of_stable
    F (owners i) (hstable i)]
  exact Ideal.map_mono (core_le_jointCore F owners i)

/-- The actual root ideal of the joint core is permissible for every owner. -/
theorem every_owner_permissible
    (hq : 0 < q)
    (F : Frame (R := R) (A := A) q t)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ι → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable
        (HasseSaturationDescent.transportedHasseAddHom F) (owners i))
    (i : ι) :
    MarkedIdeal.Permissible
      (R := A) ⟨owners i, q, hq⟩ (S.rootIdeal (jointCore F owners)) := by
  exact S.markedPacket_permissible hq
    (owner_le_jointCoreExtension F owners hstable i)

/-- Aggregate active ideal with common mark `q`. -/
def jointOwnerIdeal (owners : ι → Ideal A) : Ideal A :=
  OwnerJoint.activeUnion owners Finset.univ

/-- The finite aggregate of all active owners is permissible for the same root
centre. -/
theorem jointOwnerIdeal_permissible
    (hq : 0 < q)
    (F : Frame (R := R) (A := A) q t)
    (S : FrobeniusRootCentre.RootSection (R := R) (A := A) q)
    (owners : ι → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable
        (HasseSaturationDescent.transportedHasseAddHom F) (owners i)) :
    MarkedIdeal.Permissible
      (R := A) ⟨jointOwnerIdeal owners, q, hq⟩
      (S.rootIdeal (jointCore F owners)) := by
  exact OwnerJoint.aggregate_permissible
    owners Finset.univ (S.rootIdeal (jointCore F owners)) q hq
    (fun i hi => every_owner_permissible hq F S owners hstable i)

/-- Owner conflict is explicit: either the joint core is the unit ideal, or a
split root section yields one proper actual centre permissible for all owners. -/
theorem conflict_or_proper_jointCentre
    (hq : 0 < q)
    (F : Frame (R := R) (A := A) q t)
    (S : SplitFrobeniusRootCentre.SplitRootSection
      (R := R) (A := A) q)
    (owners : ι → Ideal A)
    (hstable : ∀ i,
      DifferentialIdealSaturation.Stable
        (HasseSaturationDescent.transportedHasseAddHom F) (owners i)) :
    jointCore F owners = ⊤ ∨
      ∃ C : Ideal A,
        C ≠ ⊤ ∧
        MarkedIdeal.Permissible
          (R := A) ⟨jointOwnerIdeal owners, q, hq⟩ C := by
  by_cases htop : jointCore F owners = ⊤
  · exact Or.inl htop
  · exact Or.inr
      ⟨S.rootIdeal (jointCore F owners),
        S.rootIdeal_ne_top htop,
        jointOwnerIdeal_permissible hq F S.toRootSection owners hstable⟩

end

end JointFrobeniusOwnerCentre
end PCRLean
