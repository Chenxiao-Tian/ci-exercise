import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Affine bigraded flatness compiler

A mixed-Rees or normal-cone packet is one direct sum of homogeneous pieces.
Flatness of the total module over the carrier is equivalent to flatness of
every bidegree.  The same statement holds simultaneously for a finite owner
portfolio.

This is the exact module-theoretic compiler behind the X038 affine
normal-cone simplification.  It does not construct a graded algebra, prove
finite generation, invoke flatification, or identify any geometric strict
transform.
-/

namespace PCRLean
namespace Experimental
namespace BigradedFlatnessCompiler

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable (Piece : (ℕ × ℕ) → Type v)
variable [∀ d, AddCommGroup (Piece d)] [∀ d, Module A (Piece d)]

/-- The complete bigraded packet is flat exactly when every bidegree is flat. -/
theorem directSumFlat_iff_pieceFlat :
    Module.Flat A (DirectSum (ℕ × ℕ) Piece) ↔
      ∀ d, Module.Flat A (Piece d) := by
  classical
  exact Module.Flat.directSum_iff

/-- Pointwise flatness compiles to flatness of the full affine packet. -/
theorem directSumFlat
    (h : ∀ d, Module.Flat A (Piece d)) :
    Module.Flat A (DirectSum (ℕ × ℕ) Piece) := by
  classical
  exact (directSumFlat_iff_pieceFlat (A := A) Piece).mpr h

/-- Flatness of the full packet projects to every bidegree. -/
theorem pieceFlat_of_directSumFlat
    [Module.Flat A (DirectSum (ℕ × ℕ) Piece)]
    (d : ℕ × ℕ) :
    Module.Flat A (Piece d) := by
  classical
  exact (directSumFlat_iff_pieceFlat (A := A) Piece).mp
    (inferInstance : Module.Flat A (DirectSum (ℕ × ℕ) Piece)) d

section Portfolio

variable {Owner : Type w} [Fintype Owner]
variable (OwnerPiece : Owner → (ℕ × ℕ) → Type v)
variable [∀ o d, AddCommGroup (OwnerPiece o d)]
variable [∀ o d, Module A (OwnerPiece o d)]

/-- Simultaneous pointwise flatness of every owner and bidegree implies
flatness of the complete finite portfolio. -/
theorem portfolioFlat
    (h : ∀ o d, Module.Flat A (OwnerPiece o d)) :
    Module.Flat A
      (DirectSum Owner
        (fun o => DirectSum (ℕ × ℕ) (OwnerPiece o))) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro o
  exact directSumFlat (A := A) (OwnerPiece o) (h o)

/-- Flatness of the complete portfolio projects to every owner and bidegree. -/
theorem ownerPieceFlat_of_portfolioFlat
    [Module.Flat A
      (DirectSum Owner
        (fun o => DirectSum (ℕ × ℕ) (OwnerPiece o)))]
    (o : Owner) (d : ℕ × ℕ) :
    Module.Flat A (OwnerPiece o d) := by
  classical
  have hOwner : Module.Flat A (DirectSum (ℕ × ℕ) (OwnerPiece o)) :=
    (Module.Flat.directSum_iff
      (R := A)
      (M := fun o => DirectSum (ℕ × ℕ) (OwnerPiece o))).mp
      (inferInstance : Module.Flat A
        (DirectSum Owner
          (fun o => DirectSum (ℕ × ℕ) (OwnerPiece o)))) o
  letI : Module.Flat A (DirectSum (ℕ × ℕ) (OwnerPiece o)) := hOwner
  exact pieceFlat_of_directSumFlat (A := A) (OwnerPiece o) d

end Portfolio

end

end BigradedFlatnessCompiler
end Experimental
end PCRLean
