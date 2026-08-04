import Mathlib

/-!
# The canonical product ideal of a finite building set

For a finite building set of closed strata with ideal sheaves `I_a`, the
product `prod_a I_a` is independent of every enumeration and is fixed by every
symmetry that transports the strata ideals.  Wonderful-model geometry
identifies the final canonical model with the blow-up of this product ideal,
while an admissible layer order supplies an implementation by ordinary smooth
centres.

This file formalizes only the finite commutative product invariant.  The
scheme-level comparison between its blow-up and the iterated ordinary-centre
word is a geometric theorem obligation.
-/

namespace PCRLean
namespace Experimental
namespace WonderfulProductIdeal

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {α : Type v} [Fintype α]

/-- Product ideal attached to all members of a finite building set. -/
def productIdeal (I : α → Ideal R) : Ideal R :=
  ∏ a, I a

/-- Pointwise equal ideal families give the same product ideal. -/
theorem productIdeal_congr
    (I J : α → Ideal R)
    (hIJ : ∀ a, I a = J a) :
    productIdeal I = productIdeal J := by
  exact Fintype.prod_congr I J hIJ

/-- Reindexing by an equivalence does not change the product ideal. -/
theorem productIdeal_equiv
    {β : Type v} [Fintype β]
    (e : α ≃ β) (I : β → Ideal R) :
    productIdeal (fun a => I (e a)) = productIdeal I := by
  exact e.prod_comp I

/-- A symmetry preserving every stratum ideal fixes the product ideal. -/
theorem productIdeal_symmetry
    (e : α ≃ α) (I : α → Ideal R)
    (hI : ∀ a, I (e a) = I a) :
    productIdeal (fun a => I (e a)) = productIdeal I := by
  exact productIdeal_congr _ _ hI

/-- For a one-stratum building set the product ideal is the stratum ideal. -/
@[simp] theorem productIdeal_unique [Unique α] (I : α → Ideal R) :
    productIdeal I = I default := by
  simp [productIdeal]

end

end WonderfulProductIdeal
end Experimental
end PCRLean
