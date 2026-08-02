import Mathlib
import PCRLean.FrobeniusRootCentre
import PCRLean.CoordinateKernelIdeal

/-!
# Coordinate Frobenius root-centre certificates

When a Frobenius root ideal is identified with a coordinate-kernel ideal, its
geometric effectivity is completely explicit: it is a proper actual ideal, its
quotient is a smaller polynomial ring, and every descended marked packet is
permissible for it.

This file packages that implication without pretending that every intrinsic
Frobenius core is already known to admit such coordinates.  Producing the
coordinate identification, compatibly on overlaps and with the boundary, is
the remaining geometric realization theorem.
-/

namespace PCRLean
namespace CoordinateFrobeniusRootCentre

noncomputable section

universe u v w x

variable {R : Type u} {K : Type v}
variable [CommRing R] [CommRing K]
variable {σ : Type w} {τ : Type x}

abbrev Ambient := MvPolynomial τ K

variable [Algebra R (Ambient (K := K) (τ := τ))]

/-- Quotient equivalence supplied by identifying a root ideal with an actual
coordinate-kernel ideal. -/
noncomputable def quotientEquiv
    {q : Nat}
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := Ambient (K := K) (τ := τ)) q)
    (J : Ideal R)
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord : S.rootIdeal J = CoordinateKernelIdeal.ideal (R := K) f hf) :
    (Ambient (K := K) (τ := τ) ⧸ S.rootIdeal J) ≃+*
      MvPolynomial σ K := by
  rw [hcoord]
  exact CoordinateKernelIdeal.quotientEquiv (R := K) f hf

/-- A coordinate-identified root ideal is proper. -/
theorem rootIdeal_ne_top
    [Nontrivial K]
    {q : Nat}
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := Ambient (K := K) (τ := τ)) q)
    (J : Ideal R)
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord : S.rootIdeal J = CoordinateKernelIdeal.ideal (R := K) f hf) :
    S.rootIdeal J ≠ ⊤ := by
  rw [hcoord]
  exact CoordinateKernelIdeal.ideal_ne_top (R := K) f hf

/-- The quotient by a coordinate-identified root ideal is explicitly a smaller
polynomial ring. -/
theorem quotient_is_smaller_polynomial_ring
    {q : Nat}
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := Ambient (K := K) (τ := τ)) q)
    (J : Ideal R)
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord : S.rootIdeal J = CoordinateKernelIdeal.ideal (R := K) f hf) :
    Nonempty
      ((Ambient (K := K) (τ := τ) ⧸ S.rootIdeal J) ≃+*
        MvPolynomial σ K) :=
  ⟨quotientEquiv S J f hf hcoord⟩

/-- Over a Noetherian coefficient ring and finitely many ambient variables, a
coordinate-identified root ideal is finitely generated. -/
theorem rootIdeal_fg
    [IsNoetherianRing K] [Finite τ]
    {q : Nat}
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := Ambient (K := K) (τ := τ)) q)
    (J : Ideal R)
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord : S.rootIdeal J = CoordinateKernelIdeal.ideal (R := K) f hf) :
    (S.rootIdeal J).FG := by
  rw [hcoord]
  exact CoordinateKernelIdeal.ideal_fg (R := K) f hf

/-- Complete affine coordinate certificate for a descended marked packet: an
actual proper permissible ideal together with an explicit quotient by a
smaller polynomial ring. -/
theorem coordinateRootCentre_certificate
    [Nontrivial K]
    {q : Nat} (hq : 0 < q)
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := Ambient (K := K) (τ := τ)) q)
    {I : Ideal (Ambient (K := K) (τ := τ))}
    {J : Ideal R}
    (hdesc : I ≤ J.map
      (algebraMap R (Ambient (K := K) (τ := τ))))
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord : S.rootIdeal J = CoordinateKernelIdeal.ideal (R := K) f hf) :
    ∃ C : Ideal (Ambient (K := K) (τ := τ)),
      C ≠ ⊤ ∧
      MarkedIdeal.Permissible
        (R := Ambient (K := K) (τ := τ)) ⟨I, q, hq⟩ C ∧
      Nonempty
        ((Ambient (K := K) (τ := τ) ⧸ C) ≃+*
          MvPolynomial σ K) := by
  refine ⟨S.rootIdeal J,
    rootIdeal_ne_top S J f hf hcoord,
    S.markedPacket_permissible hq hdesc,
    quotient_is_smaller_polynomial_ring S J f hf hcoord⟩

end

end CoordinateFrobeniusRootCentre
end PCRLean
