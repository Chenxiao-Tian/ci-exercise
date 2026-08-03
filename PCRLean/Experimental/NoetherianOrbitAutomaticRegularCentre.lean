import Mathlib
import PCRLean.FiniteKernelCentre
import PCRLean.Experimental.ArbitraryFiniteLinearPacketRegularCentre

/-!
# Experimental automatic regular centre from a Noetherian operator orbit

A Noetherian operator orbit admits a finite raw packet spanning the full orbit
module.  Pair that orbit with a finite-dimensional direction space.  The finite
evaluation map need not be split or have independent rows: its canonical range
factorization already produces an intrinsic actual proper finitely generated
centre ideal with regular quotient.  The degree-one kernel is exactly the
persistent annihilator of the full infinite orbit.

This theorem combines the algebraic U1 finite-packet mechanism with the linear
U2 actual-regular-centre mechanism.  It does not prove that an arbitrary
positive-characteristic singularity admits the required finite-dimensional
operator representation, that the centre is permissible for every marked
owner, or that it transforms kernel-exactly on blowup charts.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianOrbitAutomaticRegularCentre

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {D : Type v} {V : Type w} {ι : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V]
variable [IsNoetherian K D]
variable [FiniteDimensional K V]

abbrev DualV := Module.Dual K V

open ArbitraryFiniteLinearPacketRegularCentre

/-- Complete algebraic certificate extracted from one Noetherian operator
orbit. -/
structure Certificate
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] DualV (K := K) (V := V)) where
  packet : Finset D
  packet_raw :
    (packet : Set D) ⊆ NoetherianOperatorOrbit.orbitSet ops seed
  packet_spans :
    NoetherianOperatorOrbit.orbitModule ops seed =
      Submodule.span K (packet : Set D)
  centreIdeal : Ideal (SymmetricAlgebra K V)
  centreIdeal_eq : centreIdeal =
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
      (FiniteKernelCentre.evaluationMap pair packet)
  proper : centreIdeal ≠ ⊤
  finiteType : centreIdeal.FG
  quotient :
    (SymmetricAlgebra K V ⧸ centreIdeal) ≃+*
      SymmetricAlgebra K
        (LinearMap.range (FiniteKernelCentre.evaluationMap pair packet))
  quotientRegular : IsRegularRing (SymmetricAlgebra K V ⧸ centreIdeal)
  persistentKernel_eq :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
      LinearMap.ker (FiniteKernelCentre.evaluationMap pair packet)

/-- Every Noetherian operator orbit in the stated finite-dimensional chamber
has an actual proper finite-type regular centre certificate. -/
theorem exists_certificate
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] DualV (K := K) (V := V)) :
    Nonempty (Certificate ops seed pair) := by
  rcases NoetherianOperatorOrbit.exists_finite_raw_orbit_generators
    ops seed with ⟨s, hs, hspan⟩
  let P : FiniteKernelCentre.OrbitPacket ops seed pair where
    packet := s
    packet_raw := hs
    packet_spans := hspan
  let I : Ideal (SymmetricAlgebra K V) :=
    ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
      (FiniteKernelCentre.evaluationMap pair s)
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
    persistentKernel_eq := ?_
  }⟩
  · exact ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_ne_top
      (FiniteKernelCentre.evaluationMap pair s)
  · exact ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_fg
      (FiniteKernelCentre.evaluationMap pair s)
  · exact ArbitraryFiniteLinearPacketRegularCentre.quotientEquiv
      (FiniteKernelCentre.evaluationMap pair s)
  · exact ArbitraryFiniteLinearPacketRegularCentre.quotient_isRegularRing
      (FiniteKernelCentre.evaluationMap pair s)
  · exact P.annihilator_eq_ker_evaluation

namespace Certificate

variable {ops : ι → Module.End K D} {seed : D}
    {pair : D →ₗ[K] DualV (K := K) (V := V)}
    (C : Certificate ops seed pair)

/-- Every vector in the persistent annihilator gives a degree-one element of
the actual centre ideal. -/
theorem persistentGenerator_mem
    (x : NoetherianOperatorOrbit.annihilatorVia pair
      (NoetherianOperatorOrbit.orbitModule ops seed)) :
    SymmetricAlgebra.ι K V x.1 ∈ C.centreIdeal := by
  rw [C.centreIdeal_eq]
  unfold ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
  apply Ideal.subset_span
  refine ⟨⟨x.1, ?_⟩, rfl⟩
  rw [← C.persistentKernel_eq]
  exact x.2

/-- The actual centre contains exactly the degree-one persistent-kernel
relations used by the certificate. -/
theorem persistentKernel_eq_packetKernel :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) =
      LinearMap.ker (FiniteKernelCentre.evaluationMap pair C.packet) :=
  C.persistentKernel_eq

end Certificate

end

end NoetherianOrbitAutomaticRegularCentre
end Experimental
end PCRLean
