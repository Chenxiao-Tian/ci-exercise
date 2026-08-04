import Mathlib
import PCRLean.Experimental.FiniteGradedFlatnessCompiler

/-!
# Finite passive-portfolio flatness compiler

A resolution state carries finitely many passive owners.  Once each owner's
associated-graded module has a finite Rees--Serre certificate, the direct sum
of all owners and all degrees is flat over the candidate centre.  This packages
simultaneous passive normal flatness as one exact module-theoretic certificate.

The geometric construction of the certificates, their transport under ambient
blowups, and the flatification word remain separate X036 obligations.
-/

namespace PCRLean
namespace Experimental
namespace FinitePassivePortfolio

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {Owner : Type w} [Fintype Owner] [DecidableEq Owner]
variable (Piece Tail : Owner → ℕ → Type v)
variable [∀ o n, AddCommGroup (Piece o n)]
variable [∀ o n, Module A (Piece o n)]
variable [∀ o n, AddCommGroup (Tail o n)]
variable [∀ o n, Module A (Tail o n)]

open FiniteGradedFlatnessCompiler

/-- A cutoff and finite-tail certificate for every passive owner. -/
structure Certificate : Prop where
  cutoff : Owner → ℕ
  ownerCertificate : ∀ o,
    FiniteGradedFlatnessCompiler.Certificate
      (A := A) (Piece o) (Tail o) (cutoff o)

/-- Every owner's full graded module is flat. -/
theorem Certificate.ownerFlat
    (c : Certificate (A := A) Piece Tail)
    (o : Owner) :
    Module.Flat A (⨁ n, Piece o n) :=
  (c.ownerCertificate o).directSumFlat

/-- The complete finite passive portfolio is flat. -/
theorem Certificate.portfolioFlat
    (c : Certificate (A := A) Piece Tail) :
    Module.Flat A (⨁ o, (⨁ n, Piece o n)) := by
  classical
  rw [Module.Flat.directSum_iff]
  intro o
  exact c.ownerFlat o

end

end FinitePassivePortfolio
end Experimental
end PCRLean
