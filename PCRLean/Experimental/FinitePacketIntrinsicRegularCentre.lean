import Mathlib
import PCRLean.LinearizedGeometricRealization
import PCRLean.Experimental.FiniteDimensionalIntrinsicRegularCentre

/-!
# Experimental intrinsic regular centre from a finite operator packet

A finite Hasse--Cartier orbit packet with a split evaluation map determines a
split surjection from the ambient direction space to its finite coefficient
space.  The intrinsic degree-one kernel ideal in the symmetric algebra is then
an actual proper finite-type ideal with regular quotient, provided the ambient
direction space is finite-dimensional over the coefficient field.

This theorem compiles the existing linearized realization certificate into an
actual affine regular-centre certificate.  It still assumes the split finite
packet and does not prove that arbitrary singular Frobenius/Fitting data admit
such a packet Zariski-locally or that the centre is permissible for every
marked owner.
-/

namespace PCRLean
namespace Experimental
namespace FinitePacketIntrinsicRegularCentre

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {D : Type v} {V : Type w} {ι : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V]

abbrev DualV := Module.Dual K V

open LinearizedGeometricRealization
open SplitSurjectionSymmetricQuotient

variable {ops : ι → Module.End K D} {seed : D}
variable {pair : D →ₗ[K] DualV (K := K) (V := V)}
variable (C : LinearizedGeometricRealization.Certificate ops seed pair)

/-- The packet evaluation and its chosen section form a split surjection. -/
def splitSurjection :
    SplitSurjection
      (R := K) (V := V) (Kmod := (↥C.packet → K)) where
  project := LinearizedGeometricRealization.packetEval pair C.packet
  liftBack := C.split
  rightInverse := C.rightInverse

/-- The intrinsic actual ideal attached to the persistent packet kernel. -/
def centreIdeal : Ideal (SymmetricAlgebra K V) :=
  C.splitSurjection.kernelIdeal

/-- Every degree-one element from the finite packet kernel belongs to the
actual centre ideal. -/
theorem kernelGenerator_mem
    (x : LinearMap.ker
      (LinearizedGeometricRealization.packetEval pair C.packet)) :
    SymmetricAlgebra.ι K V x.1 ∈ C.centreIdeal := by
  apply Ideal.subset_span
  exact ⟨x, rfl⟩

/-- Every element of the persistent full-orbit annihilator contributes a
degree-one generator to the same actual centre ideal. -/
theorem persistentGenerator_mem
    (x : NoetherianOperatorOrbit.annihilatorVia pair
      (NoetherianOperatorOrbit.orbitModule ops seed)) :
    SymmetricAlgebra.ι K V x.1 ∈ C.centreIdeal := by
  have hxker : x.1 ∈ LinearMap.ker
      (LinearizedGeometricRealization.packetEval pair C.packet) := by
    rw [← C.persistentKernel_eq_evalKer]
    exact x.2
  exact C.kernelGenerator_mem ⟨x.1, hxker⟩

/-- Exact quotient by the actual persistent-kernel centre. -/
noncomputable def quotientEquiv :
    (SymmetricAlgebra K V ⧸ C.centreIdeal) ≃+*
      SymmetricAlgebra K (↥C.packet → K) :=
  C.splitSurjection.quotientEquiv

/-- A finite split operator packet on a finite-dimensional ambient direction
space yields an actual proper finite-type regular affine centre. -/
noncomputable def regularCentreCertificate
    [FiniteDimensional K V] :
    SplitSurjectionRegularCentre.Certificate C.splitSurjection :=
  FiniteDimensionalIntrinsicRegularCentre.certificate C.splitSurjection

/-- Properness of the packet centre. -/
theorem centreIdeal_ne_top [FiniteDimensional K V] :
    C.centreIdeal ≠ ⊤ :=
  FiniteDimensionalIntrinsicRegularCentre.kernelIdeal_ne_top C.splitSurjection

/-- Finite generation of the packet centre. -/
theorem centreIdeal_fg [FiniteDimensional K V] :
    C.centreIdeal.FG :=
  FiniteDimensionalIntrinsicRegularCentre.kernelIdeal_fg C.splitSurjection

/-- Regularity of the packet-centre quotient. -/
theorem quotient_isRegularRing [FiniteDimensional K V] :
    IsRegularRing (SymmetricAlgebra K V ⧸ C.centreIdeal) :=
  FiniteDimensionalIntrinsicRegularCentre.quotient_isRegularRing
    C.splitSurjection

end

end FinitePacketIntrinsicRegularCentre
end Experimental
end PCRLean
