import Mathlib
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate kernels as actual affine regular-centre models

An injective map of variable sets embeds a smaller polynomial ring into a
larger one.  Killing the complementary variables is a surjective algebra
retraction.  Its kernel is therefore an actual ideal, and the quotient by this
ideal is canonically isomorphic to the smaller polynomial ring.

This is the affine algebraic core of the assertion that a split linear kernel
cuts out a regular coordinate centre.  The geometric application still has to
choose such coordinates locally, prove overlap compatibility, and descend the
ideal sheaf.
-/

namespace PCRLean
namespace CoordinateKernelIdeal

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {σ : Type v} {τ : Type w}

/-- The algebra retraction which keeps variables in the injected coordinate
subspace and kills all complementary variables. -/
def retract (f : σ → τ) (hf : Function.Injective f) :
    MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.killCompl hf

/-- The actual coordinate-kernel ideal. -/
def ideal (f : σ → τ) (hf : Function.Injective f) :
    Ideal (MvPolynomial τ R) :=
  RingHom.ker (retract (R := R) f hf).toRingHom

/-- The retraction is a left inverse to variable renaming. -/
theorem retract_rename (f : σ → τ) (hf : Function.Injective f)
    (p : MvPolynomial σ R) :
    retract (R := R) f hf (MvPolynomial.rename f p) = p := by
  exact MvPolynomial.killCompl_rename_app hf p

/-- Consequently the coordinate retraction is surjective. -/
theorem retract_surjective (f : σ → τ) (hf : Function.Injective f) :
    Function.Surjective (retract (R := R) f hf) := by
  intro p
  exact ⟨MvPolynomial.rename f p, retract_rename (R := R) f hf p⟩

/-- Renaming into the larger coordinate ring is injective. -/
theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective
      (MvPolynomial.rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  MvPolynomial.rename_injective f hf

/-- The retraction has exactly the declared coordinate-kernel ideal. -/
@[simp] theorem ker_retract (f : σ → τ) (hf : Function.Injective f) :
    RingHom.ker (retract (R := R) f hf).toRingHom = ideal (R := R) f hf :=
  rfl

/-- First isomorphism theorem: the quotient by the actual coordinate-kernel
ideal is the smaller polynomial ring. -/
def quotientEquiv (f : σ → τ) (hf : Function.Injective f) :
    (MvPolynomial τ R ⧸ ideal (R := R) f hf) ≃+* MvPolynomial σ R :=
  RingHom.quotientKerEquivOfSurjective
    (f := (retract (R := R) f hf).toRingHom)
    (retract_surjective (R := R) f hf)

/-- The quotient equivalence sends the class of a polynomial to its coordinate
retraction. -/
@[simp] theorem quotientEquiv_mk (f : σ → τ) (hf : Function.Injective f)
    (p : MvPolynomial τ R) :
    quotientEquiv (R := R) f hf
      (Ideal.Quotient.mk (ideal (R := R) f hf) p) =
        retract (R := R) f hf p :=
  rfl

/-- The actual coordinate-kernel ideal is proper. -/
theorem ideal_ne_top [Nontrivial R]
    (f : σ → τ) (hf : Function.Injective f) :
    ideal (R := R) f hf ≠ ⊤ := by
  intro htop
  have hone : (1 : MvPolynomial τ R) ∈ ideal (R := R) f hf := by
    rw [htop]
    trivial
  have hzero : retract (R := R) f hf 1 = 0 :=
    RingHom.mem_ker.mp hone
  simpa using hzero

/-- Over a Noetherian coefficient ring with finitely many ambient variables,
the coordinate-kernel ideal is finitely generated. -/
theorem ideal_fg [IsNoetherianRing R] [Finite τ]
    (f : σ → τ) (hf : Function.Injective f) :
    (ideal (R := R) f hf).FG :=
  IsNoetherian.noetherian _

/-- The polynomial quotient has the same underlying ring-theoretic structure
as the smaller polynomial ring, with no completion or formal centre involved. -/
theorem quotient_nonempty (f : σ → τ) (hf : Function.Injective f) :
    Nonempty ((MvPolynomial τ R ⧸ ideal (R := R) f hf) ≃+*
      MvPolynomial σ R) :=
  ⟨quotientEquiv (R := R) f hf⟩

end

end CoordinateKernelIdeal
end PCRLean
