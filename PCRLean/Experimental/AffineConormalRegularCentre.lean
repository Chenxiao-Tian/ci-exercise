import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Defs
import PCRLean.Experimental.AffineConormalIdealCoordinates
import PCRLean.Experimental.FrobeniusNormalTransport
import PCRLean.Experimental.PolynomialGraphCentreQuotient

/-!
# Intrinsic regular centres from affine conormal determinants

Under the maximal-minor cover and augmented-minor consistency conditions, the
coordinate realization of an intrinsic affine conormal ideal is the graph ideal
of the unique determinantal solution.

Compose the coordinate algebra equivalence

`Sym_K(T∨) ≃ K[X_σ]`

with evaluation at that graph.  The resulting ring map to `K` has kernel exactly
the intrinsic affine conormal ideal and is surjective.  Therefore

`Sym_K(T∨) / I_aff ≃ K`.

This yields a coordinate-free actual proper finite-type regular centre
certificate.  The chosen frame is used to prove the theorem, but the ideal
itself is defined before coordinates, from `pair`, `value` and the finite source
packet.
-/

namespace PCRLean
namespace Experimental
namespace AffineConormalRegularCentre

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable {D : Type v} [AddCommGroup D] [Module K D]
variable {T : Type w} [AddCommGroup T] [Module K T]
variable {κ : Type x} [Fintype κ]
variable {σ : Type y} [Fintype σ] [DecidableEq σ] [Nonempty σ]

abbrev CotangentT := Module.Dual K T
abbrev SymT := SymmetricAlgebra K (CotangentT (K := K) (T := T))

variable (pair : D →ₗ[K] CotangentT (K := K) (T := T))
variable (value : D →ₗ[K] K)
variable (source : κ → D)
variable (Frame : T ≃ₗ[K] (σ → K))

abbrev Packet :=
  AffineConormalIdealCoordinates.coordinatePacket pair value source

variable [IsNoetherianRing K] [IsRegularRing K]
variable
  (Hrank : MaximalMinorAtlas.FullRankCover
    ((Packet pair value source).matrix Frame))
variable
  (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition
    ((Packet pair value source).matrix Frame)
    (Packet pair value source).rhs)

/-- Intrinsic actual affine conormal ideal. -/
def centreIdeal : Ideal (SymT (K := K) (T := T)) :=
  AffineConormalIdeal.indexedIdeal pair value source

/-- Coordinate algebra equivalence used only for the proof. -/
abbrev coordinateEquiv :=
  AffineConormalIdealCoordinates.coordinateAlgEquiv Frame

/-- Unique coordinate graph solution. -/
noncomputable def graph : σ → K :=
  Haug.globalGraph Hrank

/-- Intrinsic evaluation map obtained by evaluating the coordinate realization
on the determinantal graph. -/
def intrinsicEval : SymT (K := K) (T := T) →+* K :=
  (PolynomialGraphCentreQuotient.graphEval
    (graph pair value source Frame Hrank Haug)).comp
    (coordinateEquiv Frame).toRingHom

/-- Membership in an ideal mapped by the coordinate equivalence is equivalent
to membership in the original ideal. -/
theorem mem_mapped_centre_iff (x : SymT (K := K) (T := T)) :
    coordinateEquiv Frame x ∈
        Ideal.map (coordinateEquiv Frame)
          (centreIdeal pair value source) ↔
      x ∈ centreIdeal pair value source := by
  have h := FrobeniusNormalTransport.mem_map_pow_iff
    (coordinateEquiv Frame).toRingEquiv
    (centreIdeal pair value source) 1
    (coordinateEquiv Frame x)
  simpa using h

/-- Kernel of the intrinsic evaluation map is exactly the intrinsic affine
conormal ideal. -/
theorem ker_intrinsicEval_eq_centreIdeal :
    RingHom.ker (intrinsicEval pair value source Frame Hrank Haug) =
      centreIdeal pair value source := by
  ext x
  rw [RingHom.mem_ker]
  change PolynomialGraphCentreQuotient.graphEval
      (graph pair value source Frame Hrank Haug)
      (coordinateEquiv Frame x) = 0 ↔ _
  rw [← RingHom.mem_ker,
    PolynomialGraphCentreQuotient.ker_graphEval_eq_graphIdeal]
  rw [← AffineConormalIdealCoordinates.map_intrinsicIdeal_eq_graphIdeal
      Frame pair value source Hrank Haug]
  exact mem_mapped_centre_iff pair value source Frame x

/-- Intrinsic evaluation is surjective. -/
theorem intrinsicEval_surjective :
    Function.Surjective
      (intrinsicEval pair value source Frame Hrank Haug) := by
  intro a
  refine ⟨(coordinateEquiv Frame).symm (MvPolynomial.C a), ?_⟩
  simp [intrinsicEval, PolynomialGraphCentreQuotient.graphEval]

/-- Exact quotient by the intrinsic affine conormal ideal. -/
noncomputable def quotientEquiv :
    (SymT (K := K) (T := T) ⧸ centreIdeal pair value source) ≃+* K :=
  (Ideal.quotEquivOfEq
      (ker_intrinsicEval_eq_centreIdeal
        pair value source Frame Hrank Haug).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := intrinsicEval pair value source Frame Hrank Haug)
      (intrinsicEval_surjective pair value source Frame Hrank Haug))

/-- The intrinsic centre ideal is proper. -/
theorem centreIdeal_ne_top :
    centreIdeal pair value source ≠ ⊤ := by
  intro htop
  have hmem : (1 : SymT (K := K) (T := T)) ∈
      centreIdeal pair value source := by
    rw [htop]
    trivial
  rw [← ker_intrinsicEval_eq_centreIdeal
    pair value source Frame Hrank Haug] at hmem
  have hzero := RingHom.mem_ker.mp hmem
  simpa [intrinsicEval] using hzero

/-- Noetherianity of the ambient symmetric algebra gives finite type. -/
theorem centreIdeal_fg
    [IsNoetherianRing (SymT (K := K) (T := T))] :
    (centreIdeal pair value source).FG :=
  IsNoetherian.noetherian _

/-- The closed affine centre ring is regular. -/
theorem quotient_isRegularRing :
    IsRegularRing
      (SymT (K := K) (T := T) ⧸ centreIdeal pair value source) := by
  exact IsRegularRing.of_ringEquiv
    (quotientEquiv pair value source Frame Hrank Haug).symm

/-- Complete intrinsic actual-centre certificate. -/
structure Certificate where
  ideal : Ideal (SymT (K := K) (T := T))
  ideal_eq : ideal = centreIdeal pair value source
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient : (SymT (K := K) (T := T) ⧸ ideal) ≃+* K
  quotientRegular : IsRegularRing (SymT (K := K) (T := T) ⧸ ideal)
  coordinateImage :
    Ideal.map (coordinateEquiv Frame) ideal =
      PolynomialGraphCentreHeredity.graphIdeal
        (graph pair value source Frame Hrank Haug)

/-- Assemble the intrinsic regular-centre certificate. -/
noncomputable def certificate
    [IsNoetherianRing (SymT (K := K) (T := T))] :
    Certificate pair value source Frame Hrank Haug where
  ideal := centreIdeal pair value source
  ideal_eq := rfl
  proper := centreIdeal_ne_top pair value source Frame Hrank Haug
  finiteType := centreIdeal_fg pair value source
  quotient := quotientEquiv pair value source Frame Hrank Haug
  quotientRegular := quotient_isRegularRing
    pair value source Frame Hrank Haug
  coordinateImage :=
    AffineConormalIdealCoordinates.map_intrinsicIdeal_eq_graphIdeal
      Frame pair value source Hrank Haug

end

end AffineConormalRegularCentre
end Experimental
end PCRLean
