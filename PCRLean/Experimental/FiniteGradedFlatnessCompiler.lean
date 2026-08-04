import Mathlib
import Mathlib.RingTheory.Flat.Basic

/-!
# Finite-tail graded flatness compiler

Let `Piece n` be the graded pieces of a passive associated-graded module over
one candidate centre.  The entire direct sum is flat over the centre exactly
when every piece is flat.  Consequently, if finitely many low pieces are flat
and every high piece is linearly equivalent to a flat finite-tail model, then
the complete graded module is flat.

In the geometric X036 proposal the high model is supplied by the section
modules of a coherent sheaf on the projectivized normal bundle after a
Rees--Serre comparison bound.  Raynaud--Gruson flatification is then applied to
that projective sheaf, while the finitely many low pieces are flattened
separately.  This file proves only the exact module-theoretic compiler once
those geometric certificates are provided.
-/

namespace PCRLean
namespace Experimental
namespace FiniteGradedFlatnessCompiler

noncomputable section

universe u v

variable {A : Type u} [CommRing A]
variable (Piece Tail : ℕ → Type v)
variable [∀ n, AddCommGroup (Piece n)] [∀ n, Module A (Piece n)]
variable [∀ n, AddCommGroup (Tail n)] [∀ n, Module A (Tail n)]

/-- A finite Rees--Serre certificate: low pieces are flat, and every piece
strictly beyond the cutoff is identified with a flat tail model.  The
linear equivalences are data, so the certificate lives in `Type`. -/
structure Certificate (N : ℕ) where
  lowFlat : ∀ n, n ≤ N → Module.Flat A (Piece n)
  tailEquiv : ∀ n, N < n → Piece n ≃ₗ[A] Tail n
  tailFlat : ∀ n, N < n → Module.Flat A (Tail n)

/-- Every graded piece is flat once the finite certificate is available. -/
theorem Certificate.pieceFlat
    {N : ℕ}
    (c : Certificate (A := A) Piece Tail N)
    (n : ℕ) :
    Module.Flat A (Piece n) := by
  by_cases hlow : n ≤ N
  · exact c.lowFlat n hlow
  · have htail : N < n := Nat.lt_of_not_ge hlow
    letI : Module.Flat A (Tail n) := c.tailFlat n htail
    exact Module.Flat.of_linearEquiv (c.tailEquiv n htail)

/-- The full graded direct sum is flat.  This is the algebraic endpoint needed
by the normal-flatness gate. -/
theorem Certificate.directSumFlat
    {N : ℕ}
    (c : Certificate (A := A) Piece Tail N) :
    Module.Flat A (DirectSum ℕ Piece) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro n
  exact c.pieceFlat n

/-- Conversely, flatness of the complete graded direct sum implies flatness of
each piece. -/
theorem pieceFlat_of_directSumFlat
    [Module.Flat A (DirectSum ℕ Piece)]
    (n : ℕ) :
    Module.Flat A (Piece n) := by
  classical
  have hpieces : ∀ i, Module.Flat A (Piece i) :=
    (Module.Flat.directSum_iff (R := A) (M := Piece)).mp
      (inferInstance : Module.Flat A (DirectSum ℕ Piece))
  exact hpieces n

/-- The exact equivalence between graded normal flatness and pointwise
flatness of all homogeneous pieces. -/
theorem directSumFlat_iff_pieceFlat :
    Module.Flat A (DirectSum ℕ Piece) ↔ ∀ n, Module.Flat A (Piece n) := by
  classical
  exact Module.Flat.directSum_iff

end

end FiniteGradedFlatnessCompiler
end Experimental
end PCRLean
