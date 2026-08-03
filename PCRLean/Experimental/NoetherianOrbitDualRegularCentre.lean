import Mathlib
import PCRLean.NoetherianOperatorOrbit
import PCRLean.Experimental.DualPacketRegularCentre

/-!
# Experimental correctly oriented regular centre from a Noetherian orbit

A Noetherian operator orbit in a coefficient module admits a finite raw packet.
After pairing orbit elements with covectors on a finite-dimensional tangent
space, the cotangent row span of that packet defines an actual proper finitely
generated ideal in the cotangent symmetric algebra.  Its quotient is regular.

The simultaneous tangent kernel of the finite packet equals the persistent
annihilator of the entire infinite orbit.  Thus the finite actual centre and
the infinite operator invariant describe the same first-order geometric
subspace, with the tangent/cotangent orientation made explicit.

This closes the linear U1-to-U2 bridge in the represented finite-dimensional
chamber.  It does not construct the representation from an arbitrary
singularity, lift the first-order centre to a nonlinear local ring, prove
marked-owner permissibility, or establish hereditary blowup transport.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitDualRegularCentre

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {D : Type v} {T : Type w} {ι : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup T] [Module K T]
variable [IsNoetherian K D]
variable [FiniteDimensional K T]

abbrev Cotangent := Module.Dual K T

/-- Covector packet indexed by a finite raw orbit packet. -/
def packetCovector
    (pair : D →ₗ[K] Cotangent (K := K) (T := T))
    (s : Finset D) : s → Cotangent (K := K) (T := T) :=
  fun d => pair d.1

/-- Complete correctly oriented finite centre extracted from one operator
orbit. -/
structure Certificate
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Cotangent (K := K) (T := T)) where
  packet : Finset D
  packet_raw :
    (packet : Set D) ⊆ NoetherianOperatorOrbit.orbitSet ops seed
  packet_spans :
    NoetherianOperatorOrbit.orbitModule ops seed =
      Submodule.span K (packet : Set D)
  centreIdeal : Ideal
    (SymmetricAlgebra K (Cotangent (K := K) (T := T)))
  centreIdeal_eq : centreIdeal =
    DualPacketRegularCentre.centreIdeal (packetCovector pair packet)
  proper : centreIdeal ≠ ⊤
  finiteType : centreIdeal.FG
  quotient :
    (SymmetricAlgebra K (Cotangent (K := K) (T := T)) ⧸ centreIdeal) ≃+*
      SymmetricAlgebra K
        (Cotangent (K := K) (T := T) ⧸
          DualPacketRegularCentre.packetSpan
            (packetCovector pair packet))
  quotientRegular : IsRegularRing
    (SymmetricAlgebra K (Cotangent (K := K) (T := T)) ⧸ centreIdeal)
  persistentTangent_eq :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
      DualPacketRegularCentre.commonTangentKernel
        (packetCovector pair packet)

/-- Every represented Noetherian operator orbit has a correctly oriented actual
regular-centre certificate. -/
theorem exists_certificate
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] Cotangent (K := K) (T := T)) :
    Nonempty (Certificate ops seed pair) := by
  rcases NoetherianOperatorOrbit.exists_finite_raw_orbit_generators
    ops seed with ⟨s, hs, hspan⟩
  let packet := packetCovector pair s
  let I := DualPacketRegularCentre.centreIdeal packet
  refine ⟨{
    packet := s
    packet_raw := hs
    packet_spans := hspan
    centreIdeal := I
    centreIdeal_eq := rfl
    proper := ?_
    finiteType := ?_
    quotient := ?_
    quotientRegular := ?_
    persistentTangent_eq := ?_
  }⟩
  · exact DualPacketRegularCentre.centreIdeal_ne_top packet
  · exact DualPacketRegularCentre.centreIdeal_fg packet
  · exact DualPacketRegularCentre.quotientEquiv packet
  · exact DualPacketRegularCentre.quotient_isRegularRing packet
  · ext x
    rw [NoetherianOperatorOrbit.mem_annihilatorVia_iff_of_span_eq
      pair (NoetherianOperatorOrbit.orbitModule ops seed) s hspan x]
    rw [DualPacketRegularCentre.mem_commonTangentKernel_iff]
    constructor
    · intro h d
      exact h d.1 d.2
    · intro h d hd
      exact h ⟨d, hd⟩

namespace Certificate

variable {ops : ι → Module.End K D} {seed : D}
    {pair : D →ₗ[K] Cotangent (K := K) (T := T)}
    (C : Certificate ops seed pair)

/-- Every finite raw packet covector is one actual centre equation. -/
theorem packetGenerator_mem (d : C.packet) :
    SymmetricAlgebra.ι K (Cotangent (K := K) (T := T))
        (pair d.1) ∈ C.centreIdeal := by
  rw [C.centreIdeal_eq]
  exact DualPacketRegularCentre.packetGenerator_mem
    (packetCovector pair C.packet) d

/-- Membership in the persistent infinite-orbit tangent space is equivalent to
annihilation by every finite packet row. -/
theorem mem_persistentTangent_iff (x : T) :
    x ∈ NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) ↔
      ∀ d : C.packet, pair d.1 x = 0 := by
  rw [C.persistentTangent_eq]
  exact DualPacketRegularCentre.mem_commonTangentKernel_iff
    (packetCovector pair C.packet) x

end Certificate

end

end NoetherianOrbitDualRegularCentre
end Experimental
end PCRLean
