import Mathlib
import PCRLean.Experimental.ProjectiveMoritaDescent
import PCRLean.Experimental.ProjectiveSectionOrderIdeal

/-!
# Compatible-frame base change of projective section order ideals

Let `R → S`, let `x : P`, and let `f : P → Q` be `R`-linear, where `Q` is an
`S`-module. Suppose `P` and `Q` carry finite dual frames with the same finite
index and their coefficient functions satisfy

`G_i(f x) = image(F_i(x))`.

Then the intrinsic order ideal transports exactly:

`O_Q(f x) = O_P(x) S`.

No flatness hypothesis is needed for this statement: all base-change data is
contained in the compatible-frame certificate. In geometric applications one
constructs `G` from a localized or tensor-base-changed frame, after which this
theorem supplies exact overlap and localization naturality of the cokernel
order ideal.

Under faithful flatness, the three geometric states of the order ideal are all
reflected exactly:

* zero — the pure graph/effective chamber;
* proper nonzero — the genuine hybrid defect chamber; and
* unit — the no-proper-centre obstruction chamber.
-/

namespace PCRLean
namespace Experimental
namespace ProjectiveSectionOrderIdealBaseChange

noncomputable section

universe u v w x y

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable {P : Type w} [AddCommGroup P] [Module R P]
variable {Q : Type x} [AddCommGroup Q]
variable [Module R Q] [Module S Q] [IsScalarTower R S Q]
variable {ι : Type y} [Fintype ι] [DecidableEq ι]

open ProjectiveMoritaDescent
open ProjectiveSectionOrderIdeal

/-- Compatible finite dual frames and a section map. -/
structure CompatibleFrames
    (F : DualFrame (R := R) (P := P) (ι := ι))
    (G : DualFrame (R := S) (P := Q) (ι := ι)) where
  map : P →ₗ[R] Q
  coefficient : ∀ i x,
    G.functional i (map x) = algebraMap R S (F.functional i x)

namespace CompatibleFrames

variable
  {F : DualFrame (R := R) (P := P) (ι := ι)}
  {G : DualFrame (R := S) (P := Q) (ι := ι)}
  (C : CompatibleFrames F G)

/-- The finite frame coefficient ideal transports exactly. -/
theorem map_frameOrderIdeal_eq (x : P) :
    Ideal.map (algebraMap R S) (frameOrderIdeal F x) =
      frameOrderIdeal G (C.map x) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap,
      frameOrderIdeal, Ideal.span_le]
    rintro a ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    rw [← C.coefficient i x]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [frameOrderIdeal, Ideal.span_le]
    rintro a ⟨i, rfl⟩
    rw [C.coefficient i x]
    exact Ideal.mem_map_of_mem (algebraMap R S)
      (Ideal.subset_span ⟨i, rfl⟩)

/-- Main intrinsic base-change theorem for section order ideals. -/
theorem map_orderIdeal_eq (x : P) :
    Ideal.map (algebraMap R S) (orderIdeal x) =
      orderIdeal (C.map x) := by
  rw [← F.frameOrderIdeal_eq_orderIdeal x,
    ← G.frameOrderIdeal_eq_orderIdeal (C.map x)]
  exact C.map_frameOrderIdeal_eq x

/-- Vanishing of the source order ideal implies vanishing after compatible
base change. -/
theorem orderIdeal_eq_bot_of_source_eq_bot
    (x : P) (hx : orderIdeal x = ⊥) :
    orderIdeal (C.map x) = ⊥ := by
  rw [← C.map_orderIdeal_eq x, hx, Ideal.map_bot]

/-- If the scalar map is faithfully flat, vanishing after compatible base
change also reflects to the source. -/
theorem source_orderIdeal_eq_bot_of_target_eq_bot
    [Module.FaithfullyFlat R S]
    (x : P) (hx : orderIdeal (C.map x) = ⊥) :
    orderIdeal x = ⊥ := by
  calc
    orderIdeal x =
        (Ideal.map (algebraMap R S) (orderIdeal x)).comap
          (algebraMap R S) := by
      symm
      exact Ideal.comap_map_eq_self_of_faithfullyFlat
        (orderIdeal x)
    _ = (orderIdeal (C.map x)).comap (algebraMap R S) := by
      rw [C.map_orderIdeal_eq x]
    _ = ⊥ := by rw [hx]; simp

/-- Under faithful flatness, zero-section detection is equivalent before and
after compatible base change. -/
theorem orderIdeal_eq_bot_iff
    [Module.FaithfullyFlat R S]
    (x : P) :
    orderIdeal (C.map x) = ⊥ ↔ orderIdeal x = ⊥ := by
  constructor
  · exact C.source_orderIdeal_eq_bot_of_target_eq_bot x
  · exact C.orderIdeal_eq_bot_of_source_eq_bot x

/-- A unit source order ideal remains the unit ideal after arbitrary compatible
base change. -/
theorem orderIdeal_eq_top_of_source_eq_top
    (x : P) (hx : orderIdeal x = ⊤) :
    orderIdeal (C.map x) = ⊤ := by
  rw [← C.map_orderIdeal_eq x, hx, Ideal.map_top]

/-- Faithful flatness reflects the unit-ideal obstruction. -/
theorem source_orderIdeal_eq_top_of_target_eq_top
    [Module.FaithfullyFlat R S]
    (x : P) (hx : orderIdeal (C.map x) = ⊤) :
    orderIdeal x = ⊤ := by
  calc
    orderIdeal x =
        (Ideal.map (algebraMap R S) (orderIdeal x)).comap
          (algebraMap R S) := by
      symm
      exact Ideal.comap_map_eq_self_of_faithfullyFlat
        (orderIdeal x)
    _ = (orderIdeal (C.map x)).comap (algebraMap R S) := by
      rw [C.map_orderIdeal_eq x]
    _ = ⊤ := by rw [hx]; simp

/-- Unit obstruction is equivalent before and after faithfully flat base
change. -/
theorem orderIdeal_eq_top_iff
    [Module.FaithfullyFlat R S]
    (x : P) :
    orderIdeal (C.map x) = ⊤ ↔ orderIdeal x = ⊤ := by
  constructor
  · exact C.source_orderIdeal_eq_top_of_target_eq_top x
  · exact C.orderIdeal_eq_top_of_source_eq_top x

/-- The genuine proper-nonzero hybrid chamber is faithfully-flat local. -/
theorem properNonzero_iff
    [Module.FaithfullyFlat R S]
    (x : P) :
    (orderIdeal (C.map x) ≠ ⊥ ∧ orderIdeal (C.map x) ≠ ⊤) ↔
      (orderIdeal x ≠ ⊥ ∧ orderIdeal x ≠ ⊤) := by
  rw [ne_eq, ne_eq, ne_eq, ne_eq,
    not_congr (C.orderIdeal_eq_bot_iff x),
    not_congr (C.orderIdeal_eq_top_iff x)]

end CompatibleFrames

end

end ProjectiveSectionOrderIdealBaseChange
end Experimental
end PCRLean
