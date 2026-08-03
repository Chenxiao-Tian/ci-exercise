import Mathlib
import PCRLean.FinitePacketEvaluation
import PCRLean.Experimental.ArbitraryFiniteLinearPacketRegularCentre

/-!
# Experimental automatic regular centre from every finite linear packet

A finite family of linear functionals defines its evaluation map.  No linear
independence or chosen splitting is required: restrict the codomain to the
range, keep the same kernel, and apply the intrinsic symmetric-algebra quotient
theorem.  Thus every finite packet on a finite-dimensional vector space over a
field determines an actual proper finitely generated ideal with regular
quotient.

The ideal depends only on the submodule spanned by the packet rows.  Hence it
is invariant under finite changes of packet presentation.  This closes the
purely linear algebraic part of U2 for finite packets.  It does not prove that
the packet centre is permissible for a marked singularity, compatible with a
boundary, hereditary under nonlinear blowup transforms, or globally gluable.
-/

namespace PCRLean
namespace Experimental
namespace FinitePacketAutomaticRegularCentre

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type w} [Fintype ι]

abbrev Dual := Module.Dual K V

/-- Evaluation by the finite packet. -/
def packetMap (packet : ι → Dual (K := K) (V := V)) :
    V →ₗ[K] (ι → K) :=
  FinitePacketEvaluation.evalMap packet

/-- The intrinsic actual centre ideal of the packet. -/
def centreIdeal (packet : ι → Dual (K := K) (V := V)) :
    Ideal (SymmetricAlgebra K V) :=
  ArbitraryFiniteLinearPacketRegularCentre.centreIdeal (packetMap packet)

/-- The linear kernel of the packet is simultaneous annihilation by all packet
rows. -/
theorem mem_packetKer_iff
    (packet : ι → Dual (K := K) (V := V)) (x : V) :
    x ∈ LinearMap.ker (packetMap packet) ↔ ∀ i, packet i x = 0 := by
  simpa [packetMap, FinitePacketEvaluation.persistentKernel] using
    (FinitePacketEvaluation.mem_persistentKernel_iff packet x)

/-- Every degree-one packet-kernel vector belongs to the actual centre ideal. -/
theorem kernelGenerator_mem
    (packet : ι → Dual (K := K) (V := V))
    (x : LinearMap.ker (packetMap packet)) :
    SymmetricAlgebra.ι K V x.1 ∈ centreIdeal packet := by
  apply Ideal.subset_span
  exact ⟨x, rfl⟩

/-- Equal packet spans have equal simultaneous kernels. -/
theorem packetKer_eq_of_span_eq
    (p q : ι → Dual (K := K) (V := V))
    (hspan : Submodule.span K (Set.range p) =
      Submodule.span K (Set.range q)) :
    LinearMap.ker (packetMap p) = LinearMap.ker (packetMap q) := by
  ext x
  rw [mem_packetKer_iff, mem_packetKer_iff]
  constructor
  · intro hp i
    have hqi : q i ∈ Submodule.span K (Set.range q) :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [← hspan] at hqi
    induction hqi using Submodule.span_induction with
    | mem f hf =>
        rcases hf with ⟨j, rfl⟩
        exact hp j
    | zero => simp
    | add f g hf hg hfx hgx => simpa using congrArg₂ (· + ·) hfx hgx
    | smul a f hf hfx => simpa using congrArg (fun z : K => a * z) hfx
  · intro hq i
    have hpi : p i ∈ Submodule.span K (Set.range p) :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [hspan] at hpi
    induction hpi using Submodule.span_induction with
    | mem f hf =>
        rcases hf with ⟨j, rfl⟩
        exact hq j
    | zero => simp
    | add f g hf hg hfx hgx => simpa using congrArg₂ (· + ·) hfx hgx
    | smul a f hf hfx => simpa using congrArg (fun z : K => a * z) hfx

/-- The actual centre is independent of the chosen finite packet presentation. -/
theorem centreIdeal_eq_of_span_eq
    (p q : ι → Dual (K := K) (V := V))
    (hspan : Submodule.span K (Set.range p) =
      Submodule.span K (Set.range q)) :
    centreIdeal p = centreIdeal q := by
  unfold centreIdeal ArbitraryFiniteLinearPacketRegularCentre.centreIdeal
  exact IntrinsicKernelIdealFunctoriality.kernelIdealOf_eq_of_ker_eq
    (packetMap p) (packetMap q) (packetKer_eq_of_span_eq p q hspan)

section FiniteDimensional

variable [FiniteDimensional K V]

/-- Exact quotient theorem for an arbitrary finite packet.  The quotient target
is the symmetric algebra of the actual packet range, so dependent rows create
no spurious transverse directions. -/
noncomputable def quotientEquiv
    (packet : ι → Dual (K := K) (V := V)) :
    (SymmetricAlgebra K V ⧸ centreIdeal packet) ≃+*
      SymmetricAlgebra K (LinearMap.range (packetMap packet)) :=
  ArbitraryFiniteLinearPacketRegularCentre.quotientEquiv (packetMap packet)

/-- The packet centre is proper. -/
theorem centreIdeal_ne_top
    (packet : ι → Dual (K := K) (V := V)) :
    centreIdeal packet ≠ ⊤ :=
  ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_ne_top (packetMap packet)

/-- The packet centre is finitely generated. -/
theorem centreIdeal_fg
    (packet : ι → Dual (K := K) (V := V)) :
    (centreIdeal packet).FG :=
  ArbitraryFiniteLinearPacketRegularCentre.centreIdeal_fg (packetMap packet)

/-- The packet-centre quotient is regular. -/
theorem quotient_isRegularRing
    (packet : ι → Dual (K := K) (V := V)) :
    IsRegularRing (SymmetricAlgebra K V ⧸ centreIdeal packet) :=
  ArbitraryFiniteLinearPacketRegularCentre.quotient_isRegularRing (packetMap packet)

/-- Choice-free actual, proper, finite-type, regular centre certificate for the
finite packet. -/
noncomputable def certificate
    (packet : ι → Dual (K := K) (V := V)) :
    ArbitraryFiniteLinearPacketRegularCentre.Certificate (packetMap packet) :=
  ArbitraryFiniteLinearPacketRegularCentre.certificate (packetMap packet)

end FiniteDimensional

end

end FinitePacketAutomaticRegularCentre
end Experimental
end PCRLean
