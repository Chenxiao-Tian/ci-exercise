import Mathlib

/-!
# Coordinate boundary/SNC frames

A boundary frame embeds a finite family of boundary coordinates into the
passive variable set. Adjoining the centre coordinates gives an injective map
into the full ambient coordinate set. This is the algebraic coordinate
certificate behind SNC compatibility.
-/

namespace PCRLean
namespace CoordinateBoundarySNC

noncomputable section

universe u v w x

variable {K : Type u} [CommRing K]
variable {β : Type v} {α : Type w} {ι : Type x}

structure Frame where
  boundary : β → α
  boundary_injective : Function.Injective boundary

namespace Frame

variable (F : Frame (β := β) (α := α))

/-- Boundary coordinates followed by centre coordinates. -/
def combined : β ⊕ ι → α ⊕ ι
  | Sum.inl b => Sum.inl (F.boundary b)
  | Sum.inr i => Sum.inr i

/-- The combined boundary/centre coordinate family has no collisions. -/
theorem combined_injective : Function.Injective (F.combined (ι := ι)) := by
  intro x y hxy
  cases x with
  | inl bx =>
      cases y with
      | inl cy =>
          apply congrArg (fun b : β => (Sum.inl b : β ⊕ ι))
          apply F.boundary_injective
          exact Sum.inl.inj hxy
      | inr iy =>
          cases hxy
  | inr ix =>
      cases y with
      | inl cy =>
          cases hxy
      | inr iy =>
          apply congrArg (fun i : ι => (Sum.inr i : β ⊕ ι))
          exact Sum.inr.inj hxy

/-- Polynomial embedding of the boundary-plus-centre coordinate subsystem. -/
def polynomialEmbedding :
    MvPolynomial (β ⊕ ι) K →ₐ[K] MvPolynomial (α ⊕ ι) K :=
  MvPolynomial.rename (F.combined (ι := ι))

/-- The coordinate subsystem embeds faithfully. -/
theorem polynomialEmbedding_injective :
    Function.Injective (F.polynomialEmbedding (K := K) (ι := ι)) :=
  MvPolynomial.rename_injective _ (F.combined_injective (ι := ι))

/-- A boundary index can never equal a centre index in the ambient sum. -/
theorem boundary_ne_centre (b : β) (i : ι) :
    Sum.inl (F.boundary b) ≠ (Sum.inr i : α ⊕ ι) := by
  intro h
  cases h

end Frame

end

end CoordinateBoundarySNC
end PCRLean