import Mathlib
import PCRLean.Experimental.PacketCentreBoundary

/-!
# Experimental owner-union kernel collapse

Naively aggregating all owner packet rows can destroy every common-kernel
direction.  This finite-dimensional example has two owners on a four-dimensional
vector space.  Each owner projection has a two-dimensional kernel and hence a
strict intrinsic linear centre.  Their direct joint packet is the identity map,
so its intrinsic centre ideal is bottom.

Therefore joint legality cannot be implemented as unqualified row union.  A
correct compiler needs an owner-compatible hybrid, an obstruction class, an
earlier drop, or a finite centre word.
-/

namespace PCRLean
namespace Experimental
namespace OwnerUnionKernelCollapse

noncomputable section

universe u

variable {K : Type u} [Field K]

abbrev Plane := K × K
abbrev Ambient := Plane (K := K) × Plane (K := K)

/-- First owner sees the left plane and retains the right plane as its common
kernel. -/
def leftOwner : Ambient (K := K) →ₗ[K] Plane (K := K) where
  toFun z := z.1
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- Second owner sees the right plane and retains the left plane as its common
kernel. -/
def rightOwner : Ambient (K := K) →ₗ[K] Plane (K := K) where
  toFun z := z.2
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- Direct aggregation of both owner packets records all four coordinates. -/
def jointOwner : Ambient (K := K) →ₗ[K] Ambient (K := K) :=
  LinearMap.id

/-- The first owner packet is not injective. -/
theorem leftOwner_not_injective :
    ¬ Function.Injective (leftOwner (K := K)) := by
  intro hinj
  have h := hinj
    ((0, (1, 0)) : Ambient (K := K))
    0
    (by rfl)
  have hcoord := congrArg
    (fun z : Ambient (K := K) => z.2.1) h
  exact one_ne_zero (by simpa using hcoord)

/-- The second owner packet is not injective. -/
theorem rightOwner_not_injective :
    ¬ Function.Injective (rightOwner (K := K)) := by
  intro hinj
  have h := hinj
    (((1, 0), 0) : Ambient (K := K))
    0
    (by rfl)
  have hcoord := congrArg
    (fun z : Ambient (K := K) => z.1.1) h
  exact one_ne_zero (by simpa using hcoord)

/-- Each owner separately has a strict intrinsic centre. -/
theorem leftOwner_strictCentre :
    PacketCentreBoundary.StrictCentre (leftOwner (K := K)) := by
  exact (PacketCentreBoundary.strictCentre_iff_not_injective
    (leftOwner (K := K))).2 leftOwner_not_injective

/-- Each owner separately has a strict intrinsic centre. -/
theorem rightOwner_strictCentre :
    PacketCentreBoundary.StrictCentre (rightOwner (K := K)) := by
  exact (PacketCentreBoundary.strictCentre_iff_not_injective
    (rightOwner (K := K))).2 rightOwner_not_injective

/-- The joint row packet is injective. -/
theorem jointOwner_injective :
    Function.Injective (jointOwner (K := K)) := by
  intro a b hab
  simpa [jointOwner] using hab

/-- Direct owner aggregation collapses the intrinsic centre ideal to bottom. -/
theorem jointOwner_centreIdeal_eq_bot :
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
      (jointOwner (K := K)) = ⊥ := by
  exact PacketCentreBoundary.centreIdeal_eq_bot_of_injective
    (jointOwner (K := K)) jointOwner_injective

/-- Compact no-go package: both individual owner centres are strict, while the
naive joint centre is the whole ambient closed subscheme. -/
theorem individual_strict_but_joint_bottom :
    PacketCentreBoundary.StrictCentre (leftOwner (K := K)) ∧
    PacketCentreBoundary.StrictCentre (rightOwner (K := K)) ∧
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
      (jointOwner (K := K)) = ⊥ :=
  ⟨leftOwner_strictCentre, rightOwner_strictCentre,
    jointOwner_centreIdeal_eq_bot⟩

end

end OwnerUnionKernelCollapse
end Experimental
end PCRLean
