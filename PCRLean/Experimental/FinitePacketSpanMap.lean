import Mathlib

/-!
# Experimental finite packet span maps

A linear map sends two finite packets with the same source span to two packets
with the same target span.  This elementary theorem is used to prove that
Noetherian raw-orbit packet choices do not affect the resulting covector row
span, actual centre, or finite Frobenius root ideal.
-/

namespace PCRLean
namespace Experimental
namespace FinitePacketSpanMap

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable {D : Type v} {E : Type w}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup E] [Module K E]
variable {ι : Type x} {κ : Type y}
variable [Fintype ι] [Fintype κ]

/-- Equal source packet spans remain equal after applying a linear map. -/
theorem span_image_eq_of_span_eq
    (f : D →ₗ[K] E) (p : ι → D) (q : κ → D)
    (hspan : Submodule.span K (Set.range p) =
      Submodule.span K (Set.range q)) :
    Submodule.span K (Set.range fun i => f (p i)) =
      Submodule.span K (Set.range fun j => f (q j)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    have hp : p i ∈ Submodule.span K (Set.range p) :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [hspan] at hp
    induction hp using Submodule.span_induction with
    | mem d hd =>
        rcases hd with ⟨j, rfl⟩
        exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add d e hd he hdi hei =>
        rw [map_add]
        exact (Submodule.span K
          (Set.range fun j => f (q j))).add_mem hdi hei
    | smul a d hd hdi =>
        rw [map_smul]
        exact (Submodule.span K
          (Set.range fun j => f (q j))).smul_mem a hdi
  · rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    have hq : q j ∈ Submodule.span K (Set.range q) :=
      Submodule.subset_span ⟨j, rfl⟩
    rw [← hspan] at hq
    induction hq using Submodule.span_induction with
    | mem d hd =>
        rcases hd with ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add d e hd he hdi hei =>
        rw [map_add]
        exact (Submodule.span K
          (Set.range fun i => f (p i))).add_mem hdi hei
    | smul a d hd hdi =>
        rw [map_smul]
        exact (Submodule.span K
          (Set.range fun i => f (p i))).smul_mem a hdi

end

end FinitePacketSpanMap
end Experimental
end PCRLean
