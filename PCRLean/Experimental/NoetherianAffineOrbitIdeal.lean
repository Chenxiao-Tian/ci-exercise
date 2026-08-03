import Mathlib
import PCRLean.Experimental.NoetherianAffineOrbitPacket
import PCRLean.Experimental.AffineConormalIdeal
import PCRLean.Experimental.AffineConormalRegularCentre

/-!
# Packet-independent intrinsic ideals from Noetherian affine orbits

A represented Noetherian orbit with linear data

`pair : D → T∨`, `value : D → K`

defines an intrinsic affine equation for every orbit element.  Any finite raw
packet spanning the orbit generates the same ideal in `Sym_K(T∨)`, because the
affine equation map is linear and the packet spans agree.

Thus the orbit has a canonical actual affine conormal ideal independent of the
Noetherian generator choice.  If one finite coordinate realization satisfies
the maximal-minor cover and augmented-minor conditions, the canonical ideal
receives the complete proper finite-type regular-centre certificate and the
unique graph solution satisfies every equation in the infinite orbit.

This closes the finite-packet-choice part of U1 and the ideal-effectivity part
of U2 in the represented full-rank affine-orbit chamber.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianAffineOrbitIdeal

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable [IsNoetherianRing K] [IsRegularRing K]
variable {D : Type v} {T : Type w} {Op : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup T] [Module K T]
variable [IsNoetherian K D]
variable [FiniteDimensional K T]

abbrev Cotangent := Module.Dual K T
abbrev SymT := SymmetricAlgebra K (Cotangent (K := K) (T := T))

variable {ops : Op → Module.End K D} {seed : D}
variable {pair : D →ₗ[K] Cotangent (K := K) (T := T)}
variable {value : D →ₗ[K] K}

/-- Intrinsic actual affine ideal associated to one finite orbit certificate. -/
def ideal
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    Ideal (SymT (K := K) (T := T)) :=
  AffineConormalIdeal.packetIdeal pair value C.packet

/-- Equal orbit-module spans make the intrinsic affine ideals equal. -/
theorem ideal_eq
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    ideal (value := value) C = ideal (value := value) E := by
  apply AffineConormalIdeal.packetIdeal_eq_of_span_eq pair value
  exact C.packet_spans.symm.trans E.packet_spans

/-- Fixed representative of the canonical Noetherian affine orbit ideal. -/
noncomputable def canonicalIdeal :
    Ideal (SymT (K := K) (T := T)) :=
  ideal (value := value)
    (NoetherianOrbitPacketCanonicity.chosenCertificate
      (ops := ops) (seed := seed) (pair := pair))

/-- Every finite orbit certificate generates the canonical affine ideal. -/
theorem ideal_eq_canonical
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    ideal (value := value) C =
      canonicalIdeal (ops := ops) (seed := seed)
        (pair := pair) (value := value) :=
  ideal_eq C
    (NoetherianOrbitPacketCanonicity.chosenCertificate
      (ops := ops) (seed := seed) (pair := pair))

/-- Subtype source family used by the indexed coordinate compiler. -/
def sourceFamily
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    C.packet → D :=
  fun d => d.1

/-- Indexed and Finset forms of the affine ideal are definitionally the same. -/
theorem indexedIdeal_eq_ideal
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    AffineConormalIdeal.indexedIdeal pair value (sourceFamily C) =
      ideal (value := value) C := by
  rfl

section Coordinates

variable {σ : Type y} [Fintype σ] [DecidableEq σ] [Nonempty σ]
variable (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
variable (Frame : T ≃ₗ[K] (σ → K))

abbrev CoordinatePacket :=
  AffineConormalIdealCoordinates.coordinatePacket
    pair value (sourceFamily C)

variable
  (Hrank : MaximalMinorAtlas.FullRankCover
    ((CoordinatePacket (value := value) C).matrix Frame))
variable
  (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition
    ((CoordinatePacket (value := value) C).matrix Frame)
    (CoordinatePacket (value := value) C).rhs)
variable [IsNoetherianRing (SymT (K := K) (T := T))]

/-- Complete intrinsic regular-centre certificate for the represented affine
orbit. -/
noncomputable def regularCentreCertificate :
    AffineConormalRegularCentre.Certificate
      pair value (sourceFamily C) Frame Hrank Haug :=
  AffineConormalRegularCentre.certificate
    pair value (sourceFamily C) Frame Hrank Haug

/-- The certified ideal is the packet-independent Noetherian affine orbit
ideal. -/
theorem regularCentreCertificate_ideal_eq :
    (regularCentreCertificate
      (value := value) C Frame Hrank Haug).ideal =
      ideal (value := value) C := by
  exact (regularCentreCertificate
    (value := value) C Frame Hrank Haug).ideal_eq.trans
      (indexedIdeal_eq_ideal C)

/-- Hence the certified ideal is also the canonical orbit ideal. -/
theorem regularCentreCertificate_ideal_eq_canonical :
    (regularCentreCertificate
      (value := value) C Frame Hrank Haug).ideal =
      canonicalIdeal (ops := ops) (seed := seed)
        (pair := pair) (value := value) := by
  rw [regularCentreCertificate_ideal_eq
    (value := value) C Frame Hrank Haug,
    ideal_eq_canonical]

end Coordinates

end

end NoetherianAffineOrbitIdeal
end Experimental
end PCRLean
