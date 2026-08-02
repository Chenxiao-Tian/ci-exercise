import Mathlib
import PCRLean.NoetherianOperatorOrbit
import PCRLean.SplitKernelCentre

/-!
# Finite operator packets and split kernel centres

A Noetherian operator orbit admits a finite packet.  Pair that packet with an
ambient direction space.  The finite evaluation map cuts out the persistent
kernel.  If the evaluation map is split surjective, the kernel is a direct
summand and hence the local linear model of a regular centre.

The geometric problem is to prove this split-surjectivity locally on the
correct constant-rank stratum and to glue the resulting frames.
-/

namespace PCRLean
namespace FiniteKernelCentre

noncomputable section

universe u v w

variable {K : Type u} {D : Type v} {V : Type w}
variable [Field K]
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V]

abbrev DualV := Module.Dual K V

/-- Evaluation by a finite packet of coefficient traces. -/
def evaluationMap (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D) : V →ₗ[K] (d : s) → K where
  toFun x d := pair d.1 x
  map_add' x y := by
    ext d
    simp
  map_smul' a x := by
    ext d
    simp

@[simp] theorem evaluationMap_apply
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D) (x : V) (d : s) :
    evaluationMap pair s x d = pair d.1 x := rfl

/-- The kernel of finite evaluation is exactly the common kernel of the finite
packet. -/
theorem mem_ker_evaluationMap_iff
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D) (x : V) :
    x ∈ LinearMap.ker (evaluationMap pair s) ↔
      ∀ d ∈ s, pair d x = 0 := by
  constructor
  · intro hx d hd
    have hz : evaluationMap pair s x = 0 := hx
    have happ := congrFun hz ⟨d, hd⟩
    simpa using happ
  · intro h
    apply LinearMap.mem_ker.mpr
    ext d
    exact h d.1 d.2

/-- A finite packet whose evaluation map has a chosen section. -/
structure SplitPacket (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D) where
  section : ((d : s) → K) →ₗ[K] V
  rightInverse : (evaluationMap pair s).comp section = LinearMap.id

namespace SplitPacket

variable {pair : D →ₗ[K] DualV (K := K) (V := V)}
    {s : Finset D} (P : SplitPacket pair s)

/-- The corresponding split linear map. -/
def toSplitMap : SplitKernelCentre.SplitMap
    (K := K) (V := V) (W := (d : s) → K) where
  map := evaluationMap pair s
  section := P.section
  rightInverse := P.rightInverse

/-- Explicit product decomposition by the packet kernel and coefficient
space. -/
def equivKernelProd :
    V ≃ₗ[K] (LinearMap.ker (evaluationMap pair s) × ((d : s) → K)) :=
  P.toSplitMap.equivKernelProd

/-- The packet kernel is complementary to the image of the chosen section. -/
theorem isCompl_kernel_range_section :
    IsCompl (LinearMap.ker (evaluationMap pair s))
      (LinearMap.range P.section) :=
  P.toSplitMap.isCompl_kernel_range_section

end SplitPacket

section Orbit

variable {ι : Type*} [IsNoetherian K D]

/-- A finite raw orbit packet supplied by Noetherianity. -/
structure OrbitPacket (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] DualV (K := K) (V := V)) where
  packet : Finset D
  packet_raw : (packet : Set D) ⊆
    NoetherianOperatorOrbit.orbitSet ops seed
  packet_spans :
    NoetherianOperatorOrbit.orbitModule ops seed =
      Submodule.span K (packet : Set D)

/-- Existence of a finite raw orbit packet. -/
theorem exists_orbitPacket
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] DualV (K := K) (V := V)) :
    Nonempty (OrbitPacket ops seed pair) := by
  rcases NoetherianOperatorOrbit.exists_finite_raw_orbit_generators
    ops seed with ⟨s, hs, hspan⟩
  exact ⟨⟨s, hs, hspan⟩⟩

namespace OrbitPacket

variable {ops : ι → Module.End K D} {seed : D}
    {pair : D →ₗ[K] DualV (K := K) (V := V)}
    (P : OrbitPacket ops seed pair)

/-- The infinite orbit annihilator equals the kernel of the finite evaluation
map. -/
theorem annihilator_eq_ker_evaluation :
    NoetherianOperatorOrbit.annihilatorVia pair
      (NoetherianOperatorOrbit.orbitModule ops seed) =
      LinearMap.ker (evaluationMap pair P.packet) := by
  ext x
  rw [NoetherianOperatorOrbit.mem_annihilatorVia_iff_of_span_eq
    pair (NoetherianOperatorOrbit.orbitModule ops seed)
    P.packet P.packet_spans]
  exact (mem_ker_evaluationMap_iff pair P.packet x).symm

/-- If the finite evaluation packet is split, the persistent infinite-orbit
kernel is a split linear centre. -/
theorem persistentKernel_isCompl
    (S : SplitPacket pair P.packet) :
    IsCompl
      (NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed))
      (LinearMap.range S.section) := by
  rw [P.annihilator_eq_ker_evaluation]
  exact S.isCompl_kernel_range_section

end OrbitPacket

end Orbit

end

end FiniteKernelCentre
end PCRLean
