import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.FaithfullyFlatMarkedCentreDescent
import PCRLean.Experimental.FaithfullyFlatTransversalityDescent
import PCRLean.Experimental.PolynomialGraphBoundaryFrobeniusCertificate

/-!
# Faithfully flat descent of graph active-boundary certificates

This module states the exact local-to-global data required from an adapted
faithfully flat graph atlas.  Let `C`, `S`, and `D` be the base centre, source
packet, and boundary ideals.  On a polynomial graph chart they become:

* the graph ideal;
* the graph-root source packet; and
* a boundary ideal extended from the coefficient ring.

One additional equality is required:

`map(C ⊓ D) = map(C) ⊓ map(D)`.

This is the precise flatness/Tor interface.  Given these data, the local graph
certificate descends to:

* active marked permissibility;
* centre strictness and finite type;
* Frobenius-normality;
* properness of the combined centre-boundary ideal; and
* ideal-theoretic transversality `C ⊓ D = C * D`.

Regularity of the combined quotient and conormal local freeness still require
scheme-level descent theorems; they are not inferred here.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatGraphBoundaryDescent

noncomputable section

universe u v w x

variable {A : Type u} {R : Type v}
variable [CommRing A] [CommRing R] [IsDomain R]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev GP := MvPolynomial ι R

variable [Algebra A (GP (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (GP (R := R) (ι := ι))]

open FaithfullyFlatMarkedCentreDescent
open FaithfullyFlatTransversalityDescent
open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphBoundaryStratum
open BoundaryTransversalityGate

/-- Exact adapted graph model including the boundary and the intersection/Tor
comparison. -/
structure BoundaryGraphModel
    (C S D : Ideal A) (h : ι → R) (J : Ideal R) (q : Nat) where
  active :
    FaithfullyFlatMarkedCentreDescent.GraphModel C S h q
  boundary_extension :
    D.map (algebraMap A (GP (R := R) (ι := ι))) =
      J.map MvPolynomial.C
  intersection_extension :
    (C ⊓ D).map (algebraMap A (GP (R := R) (ι := ι))) =
      C.map (algebraMap A (GP (R := R) (ι := ι))) ⊓
        D.map (algebraMap A (GP (R := R) (ι := ι)))

namespace BoundaryGraphModel

variable {C S D : Ideal A} {h : ι → R} {J : Ideal R} {q : Nat}
variable (M : BoundaryGraphModel C S D h J q)

/-- The combined base ideal extends to the graph-boundary combined ideal. -/
theorem combined_extension :
    (C ⊔ D).map (algebraMap A (GP (R := R) (ι := ι))) =
      PolynomialGraphBoundaryStratum.combinedIdeal h J := by
  rw [Ideal.map_sup, M.active.centre_extension, M.boundary_extension]
  rfl

/-- Transversality descends from the graph chart once the intersection
comparison is supplied. -/
theorem transverse : Transverse C D := by
  apply FaithfullyFlatTransversalityDescent.transverse_of_map
    (B := GP (R := R) (ι := ι)) C D M.intersection_extension
  rw [M.active.centre_extension, M.boundary_extension]
  exact PolynomialGraphBoundaryStratum.graphIdeal_transverse_mappedBoundary h J

end BoundaryGraphModel

variable [IsNoetherianRing A]
variable [IsNoetherianRing R] [IsRegularRing R]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Descended active-boundary certificate. -/
structure DescendedCertificate
    (C S D : Ideal A) (h : ι → R) (J : Ideal R)
    (e mark : Nat) where
  active :
    FaithfullyFlatMarkedCentreDescent.DescendedCertificate
      p C S h e mark
  combinedProper : C ⊔ D ≠ ⊤
  combinedFiniteType : (C ⊔ D).FG
  transverse : Transverse C D

/-- Assemble the descended active-boundary certificate. -/
noncomputable def descend
    (C S D : Ideal A) (h : ι → R) (J : Ideal R)
    (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (hJ : J ≠ ⊤)
    (M : BoundaryGraphModel C S D h J (p ^ e)) :
    DescendedCertificate p C S D h J e mark where
  active :=
    FaithfullyFlatMarkedCentreDescent.descendGraphModel
      p C S h e mark hmark_pos hmark_le M.active
  combinedProper := by
    apply FaithfullyFlatMarkedCentreDescent.ne_top_of_map_ne_top
      (B := GP (R := R) (ι := ι)) (C ⊔ D)
    rw [M.combined_extension]
    exact PolynomialGraphBoundaryStratum.combinedIdeal_ne_top h J hJ
  combinedFiniteType := IsNoetherian.noetherian _
  transverse := M.transverse

end

end FaithfullyFlatGraphBoundaryDescent
end Experimental
end PCRLean
