import Mathlib
import Mathlib.RingTheory.Flat.Basic
import PCRLean.Experimental.HomogenizedGradedFlatness

/-!
# Degreewise regular-flag flat-lift compiler

The scheme-level Regular-Flag Flat-Lift theorem is expected to construct, on
every relevant blowup chart, a Cartier-twist-compatible linear equivalence
between each old normally-flat graded piece and the corresponding new normal
graded piece.  Once those degreewise equivalences exist, flatness of every new
piece, the complete associated graded direct sum, and its homogenized
projective completion are formal consequences.

This file proves precisely that backend.  It does not construct a regular flag,
a blowup chart, the exceptional twist, the degreewise comparison maps, overlap
cocycles, or a positive-characteristic resolution algorithm.
-/

namespace PCRLean
namespace Experimental
namespace DegreewiseFlagFlatLiftCompiler

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable (Old New : ℕ → Type v)
variable [∀ n, AddCommGroup (Old n)] [∀ n, Module A (Old n)]
variable [∀ n, AddCommGroup (New n)] [∀ n, Module A (New n)]

/-- The exact degreewise output required from the geometric regular-flag chart
theorem. -/
structure Transport where
  equiv : ∀ n, Old n ≃ₗ[A] New n

namespace Transport

variable (T : Transport (A := A) Old New)

/-- Flatness transports across each degreewise equivalence. -/
theorem newPieceFlat
    (hOld : ∀ n, Module.Flat A (Old n))
    (n : ℕ) :
    Module.Flat A (New n) := by
  letI : Module.Flat A (Old n) := hOld n
  exact Module.Flat.of_linearEquiv (T.equiv n).symm

/-- A degreewise regular-flag comparison transports normal flatness of the
complete associated graded module. -/
theorem newGradedFlat
    (hOld : ∀ n, Module.Flat A (Old n)) :
    Module.Flat A (DirectSum ℕ New) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro n
  exact T.newPieceFlat hOld n

/-- The same comparison transports flatness of the canonical homogenized
projective-normal module. -/
theorem newHomogenizedFlat
    (hOld : ∀ n, Module.Flat A (Old n)) :
    Module.Flat A
      (HomogenizedGradedFlatness.Homogenized New) :=
  HomogenizedGradedFlatness.homogenizedFlat New
    (T.newPieceFlat hOld)

end Transport

/-- Simultaneous degreewise transport for a finite owner portfolio. -/
structure PortfolioTransport
    (Owner : Type w) [Fintype Owner]
    (OldP NewP : Owner → ℕ → Type v)
    [∀ o n, AddCommGroup (OldP o n)] [∀ o n, Module A (OldP o n)]
    [∀ o n, AddCommGroup (NewP o n)] [∀ o n, Module A (NewP o n)] where
  ownerTransport : ∀ o, Transport (A := A) (OldP o) (NewP o)

namespace PortfolioTransport

variable {Owner : Type w} [Fintype Owner] [DecidableEq Owner]
variable (OldP NewP : Owner → ℕ → Type v)
variable [∀ o n, AddCommGroup (OldP o n)]
variable [∀ o n, Module A (OldP o n)]
variable [∀ o n, AddCommGroup (NewP o n)]
variable [∀ o n, Module A (NewP o n)]
variable (T : PortfolioTransport (A := A) Owner OldP NewP)

/-- All owners and all new normal degrees are flat. -/
theorem ownerPieceFlat
    (hOld : ∀ o n, Module.Flat A (OldP o n)) :
    ∀ o n, Module.Flat A (NewP o n) := by
  intro o n
  exact (T.ownerTransport o).newPieceFlat (hOld o) n

/-- The complete finite owner portfolio of new associated-graded modules is
flat over the carrier. -/
theorem portfolioFlat
    (hOld : ∀ o n, Module.Flat A (OldP o n)) :
    Module.Flat A
      (DirectSum Owner (fun o => DirectSum ℕ (NewP o))) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro o
  exact (T.ownerTransport o).newGradedFlat (hOld o)

end PortfolioTransport

end

end DegreewiseFlagFlatLiftCompiler
end Experimental
end PCRLean
