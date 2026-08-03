import Mathlib
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import PCRLean.Experimental.ArbitraryFiniteLinearPacketRegularCentre
import PCRLean.Experimental.FinitePacketAutomaticRegularCentre

/-!
# Experimental boundary of automatic finite-packet centres

Every finite linear packet on a finite-dimensional vector space has an
intrinsic degree-one ideal with regular quotient. That algebraic regularity is
not yet a legal blowup-centre theorem: the ideal may be bottom, in which case
the corresponding closed subscheme is the whole ambient affine space.

This file isolates the missing `nonWhole` gate. The intrinsic centre ideal is
bottom exactly when the packet map is injective. Hence a strict packet centre
exists exactly when the packet retains a genuine common-kernel direction. The
identity packet supplies a minimal counterexample to the invalid implication

`regular quotient -> legal nontrivial centre`.

The statements below do not assert marked permissibility, singular-locus
containment, boundary compatibility, or hereditary blowup transport.
-/

namespace PCRLean
namespace Experimental
namespace PacketCentreBoundary

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

open IntrinsicKernelIdealFunctoriality
open ArbitraryFiniteLinearPacketRegularCentre

/-- A strict affine centre ideal is neither the whole ring nor the zero ideal.
The second condition is the missing gate in the earlier automatic-centre
certificate. -/
def StrictCentre (project : V →ₗ[K] W) : Prop :=
  centreIdeal project ≠ ⊥ ∧ centreIdeal project ≠ ⊤

/-- Every degree-one vector in the packet kernel belongs to the intrinsic
centre ideal. -/
theorem kernelGenerator_mem
    (project : V →ₗ[K] W)
    (z : LinearMap.ker project) :
    SymmetricAlgebra.ι K V z.1 ∈ centreIdeal project := by
  unfold centreIdeal kernelIdealOf
  apply Ideal.subset_span
  exact ⟨z, rfl⟩

/-- The degree-one embedding into a symmetric algebra is injective for a free
module over a field. The proof separates vectors by basis-coordinate linear
functionals and the universal property of the symmetric algebra. -/
theorem symmetricIota_injective [Module.Free K V] :
    Function.Injective (SymmetricAlgebra.ι K V) := by
  let basis := Module.Free.chooseBasis K V
  intro a b hab
  apply basis.repr.injective
  ext i
  let coordinate : V →ₗ[K] K where
    toFun z := basis.repr z i
    map_add' := by
      intro z t
      simp
    map_smul' := by
      intro c z
      simp
  have h := congrArg
    (fun z : SymmetricAlgebra K V =>
      (SymmetricAlgebra.lift coordinate) z) hab
  simpa [coordinate] using h

/-- An injective packet map has zero kernel, so the intrinsic degree-one ideal
is bottom. Algebraically regular quotient data alone therefore need not give a
usable centre. -/
theorem centreIdeal_eq_bot_of_injective
    (project : V →ₗ[K] W)
    (hinj : Function.Injective project) :
    centreIdeal project = ⊥ := by
  unfold centreIdeal kernelIdealOf
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z ⟨k, rfl⟩
    have hk0 : project k.1 = project 0 := by
      simpa using LinearMap.mem_ker.mp k.2
    have hk : k.1 = 0 := hinj hk0
    rw [hk]
    simp
  · exact bot_le

/-- Conversely, if the intrinsic ideal is bottom then the packet map is
injective. The only substantive input is injectivity of the symmetric-algebra
degree-one embedding. -/
theorem injective_of_centreIdeal_eq_bot
    [Module.Free K V]
    (project : V →ₗ[K] W)
    (hbot : centreIdeal project = ⊥) :
    Function.Injective project := by
  intro a b hab
  have hker : a - b ∈ LinearMap.ker project := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub, hab, sub_self]
  have hmem := kernelGenerator_mem project ⟨a - b, hker⟩
  rw [hbot] at hmem
  have hi :
      SymmetricAlgebra.ι K V (a - b) =
        SymmetricAlgebra.ι K V 0 := by
    simpa using hmem
  have hz : a - b = 0 := symmetricIota_injective hi
  exact sub_eq_zero.mp hz

/-- Exact algebraic boundary: the intrinsic packet centre is the whole ambient
closed subscheme precisely when the packet separates all directions. -/
theorem centreIdeal_eq_bot_iff_injective
    [Module.Free K V]
    (project : V →ₗ[K] W) :
    centreIdeal project = ⊥ ↔ Function.Injective project := by
  constructor
  · exact injective_of_centreIdeal_eq_bot project
  · exact centreIdeal_eq_bot_of_injective project

/-- The identity packet is the minimal full-rank boundary example. -/
theorem identityCentreIdeal_eq_bot :
    centreIdeal (LinearMap.id : V →ₗ[K] V) = ⊥ := by
  apply centreIdeal_eq_bot_of_injective
  intro a b hab
  simpa using hab

/-- A non-bottom intrinsic packet ideal forces failure of injectivity. Thus a
legal nonwhole packet centre requires an actual common-kernel direction. -/
theorem not_injective_of_centreIdeal_ne_bot
    (project : V →ₗ[K] W)
    (hcentre : centreIdeal project ≠ ⊥) :
    ¬ Function.Injective project := by
  intro hinj
  exact hcentre (centreIdeal_eq_bot_of_injective project hinj)

/-- At the opposite rank boundary, the zero packet cuts out the linear origin:
its ideal is generated by every degree-one element. -/
theorem zeroCentreIdeal_eq_span_iota :
    centreIdeal (0 : V →ₗ[K] W) =
      Ideal.span (Set.range fun v : V => SymmetricAlgebra.ι K V v) := by
  unfold centreIdeal kernelIdealOf
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v, by simp⟩, rfl⟩

section FiniteDimensional

variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- In finite dimension the earlier theorem supplies properness automatically,
so strictness is exactly the additional non-bottom condition. -/
theorem strictCentre_iff_ne_bot (project : V →ₗ[K] W) :
    StrictCentre project ↔ centreIdeal project ≠ ⊥ := by
  constructor
  · exact fun h => h.1
  · intro hbot
    exact ⟨hbot, centreIdeal_ne_top project⟩

/-- In finite dimension the strict-centre gate is exactly failure of
injectivity of the packet map. This is the precise algebraic boundary that a
geometric packetization theorem must control. -/
theorem strictCentre_iff_not_injective
    (project : V →ₗ[K] W) :
    StrictCentre project ↔ ¬ Function.Injective project := by
  exact (strictCentre_iff_ne_bot project).trans
    (not_congr (centreIdeal_eq_bot_iff_injective project))

/-- Minimal falsifier: the identity packet has a regular quotient but its
centre ideal is bottom. Therefore regularity and properness of the quotient do
not imply a legal nonwhole blowup centre. -/
theorem identityPacket_regular_quotient_but_not_strict :
    IsRegularRing
        (SymmetricAlgebra K V ⧸
          centreIdeal (LinearMap.id : V →ₗ[K] V)) ∧
      ¬ StrictCentre (LinearMap.id : V →ₗ[K] V) := by
  constructor
  · exact quotient_isRegularRing
      (LinearMap.id : V →ₗ[K] V)
  · intro hstrict
    exact hstrict.1 identityCentreIdeal_eq_bot

end FiniteDimensional

section FinitePacket

variable {ι : Type x} [Fintype ι]

open FinitePacketAutomaticRegularCentre

/-- Packet form of the nonwhole-centre boundary. -/
theorem packetMap_not_injective_of_centreIdeal_ne_bot
    (packet : ι → Module.Dual K V)
    (hcentre : FinitePacketAutomaticRegularCentre.centreIdeal packet ≠ ⊥) :
    ¬ Function.Injective
      (FinitePacketAutomaticRegularCentre.packetMap packet) := by
  exact not_injective_of_centreIdeal_ne_bot
    (FinitePacketAutomaticRegularCentre.packetMap packet) hcentre

end FinitePacket

end

end PacketCentreBoundary
end Experimental
end PCRLean
