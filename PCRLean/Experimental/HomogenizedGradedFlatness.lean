import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Homogenized all-degree flatness

Let `Piece n` be the homogeneous pieces of a finite graded module on an affine
normal cone.  The canonical projective completion obtained by adjoining one
homogenizing variable has degree-`d` slice

`Piece 0 ⊕ Piece 1 ⊕ ... ⊕ Piece d`.

As a module over the carrier, its complete homogeneous module is therefore the
direct sum of these finite triangular slices.  Flatness of this homogenized
module is equivalent to flatness of every original graded piece.

Geometrically, the X041 candidate sheafifies this module on
`P(O ⊕ I/I²)`; the chart where the homogenizing coordinate is invertible is the
full affine normal cone, so no low-degree window or projective-tail cutoff is
lost.  This file proves only the exact module-theoretic flatness compiler.  It
does not construct symmetric algebras, Proj, associated graded sheaves,
functorial flatifiers, blowups, or a resolution algorithm.
-/

namespace PCRLean
namespace Experimental
namespace HomogenizedGradedFlatness

noncomputable section

universe u v

variable {A : Type u} [CommRing A]
variable (Piece : ℕ → Type v)
variable [∀ n, AddCommGroup (Piece n)]
variable [∀ n, Module A (Piece n)]

/-- The degree-`d` triangular slice of the homogenization. -/
abbrev Slice (d : ℕ) :=
  DirectSum (Fin (d + 1)) (fun i => Piece i.1)

/-- The complete homogenized carrier module. -/
abbrev Homogenized :=
  DirectSum ℕ (fun d => Slice Piece d)

/-- Flatness of every original piece gives flatness of every finite triangular
slice. -/
theorem sliceFlat
    (hPiece : ∀ n, Module.Flat A (Piece n))
    (d : ℕ) :
    Module.Flat A (Slice Piece d) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro i
  exact hPiece i.1

/-- Pointwise flatness compiles to flatness of the complete homogenized module. -/
theorem homogenizedFlat
    (hPiece : ∀ n, Module.Flat A (Piece n)) :
    Module.Flat A (Homogenized Piece) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro d
  exact sliceFlat Piece hPiece d

/-- Flatness of the complete homogenization recovers flatness of every original
piece by reading the last summand of the degree-`n` slice. -/
theorem pieceFlat_of_homogenizedFlat
    [Module.Flat A (Homogenized Piece)]
    (n : ℕ) :
    Module.Flat A (Piece n) := by
  classical
  have hSlices : ∀ d, Module.Flat A (Slice Piece d) :=
    (Module.Flat.directSum_iff (R := A)
      (M := fun d => Slice Piece d)).mp
      (inferInstance : Module.Flat A (Homogenized Piece))
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hPieces : ∀ j : Fin (n + 1), Module.Flat A (Piece j.1) :=
    (Module.Flat.directSum_iff (R := A)
      (M := fun j : Fin (n + 1) => Piece j.1)).mp (hSlices n)
  exact hPieces i

/-- Exact module-theoretic equivalence behind the homogenized projective-normal
packet. -/
theorem homogenizedFlat_iff_pieceFlat :
    Module.Flat A (Homogenized Piece) ↔
      ∀ n, Module.Flat A (Piece n) := by
  constructor
  · intro h n
    letI : Module.Flat A (Homogenized Piece) := h
    exact pieceFlat_of_homogenizedFlat Piece n
  · exact homogenizedFlat Piece

end

end HomogenizedGradedFlatness
end Experimental
end PCRLean
