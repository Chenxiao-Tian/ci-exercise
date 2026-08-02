import Mathlib
import PCRLean.NoetherianOperatorOrbit
import PCRLean.SplitKernelCentre

/-!
# Finite operator packets and split kernel centres

A Noetherian operator orbit admits a finite packet. Pair that packet with an
ambient direction space. The finite evaluation map cuts out the persistent
kernel. A linearly independent trace packet has a surjective evaluation map,
so it admits a linear right inverse and its kernel is automatically a direct
summand.

The geometric problem is to realize the finite packet as a locally free
constant-rank coefficient bundle and to glue the resulting linear centres as
actual regular closed subschemes.
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

/-- Coercion of linear functionals to ordinary functions, as a linear map. -/
def dualToFun : DualV (K := K) (V := V) →ₗ[K] (V → K) where
  toFun f := fun x => f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coercion of linear functionals to functions is injective. -/
theorem dualToFun_injective :
    Function.Injective (dualToFun (K := K) (V := V)) := by
  intro f g h
  ext x
  exact congrFun h x

set_option maxHeartbeats 800000 in
/-- A linearly independent finite family of functionals gives a surjective
coordinate-evaluation map. -/
theorem evaluationMap_surjective_of_linearIndependent
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D)
    (hli : LinearIndependent K (fun d : s => pair d.1)) :
    Function.Surjective (evaluationMap pair s) := by
  rw [← LinearMap.range_eq_top]
  let coeDual := dualToFun (K := K) (V := V)
  let f : s → V → K := fun d => coeDual (pair d.1)
  have hliFun : LinearIndependent K f := by
    have hmap := hli.map_injOn coeDual
      (dualToFun_injective (K := K) (V := V)).injOn
    simpa [f, coeDual, Function.comp_def] using hmap
  have hspan :
      Submodule.span K (Set.range (flip f)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent).2 hliFun
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro y ⟨x, rfl⟩
  exact ⟨x, by
    ext d
    rfl⟩

/-- A finite packet whose evaluation map has a chosen right inverse. -/
structure SplitPacket (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D) where
  rightInv : ((d : s) → K) →ₗ[K] V
  rightInv_spec : (evaluationMap pair s).comp rightInv = LinearMap.id

/-- Every linearly independent finite trace packet admits a split packet
certificate. -/
theorem exists_splitPacket_of_linearIndependent
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D)
    (hli : LinearIndependent K (fun d : s => pair d.1)) :
    Nonempty (SplitPacket pair s) := by
  have hsurj := evaluationMap_surjective_of_linearIndependent pair s hli
  rcases (evaluationMap pair s).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj) with ⟨rightInv, hrightInv⟩
  exact ⟨⟨rightInv, hrightInv⟩⟩

namespace SplitPacket

variable {pair : D →ₗ[K] DualV (K := K) (V := V)}
    {s : Finset D} (P : SplitPacket pair s)

/-- The corresponding split linear map. -/
def toSplitMap : SplitKernelCentre.SplitMap
    (K := K) (V := V) (W := (d : s) → K) where
  map := evaluationMap pair s
  rightInv := P.rightInv
  rightInv_spec := P.rightInv_spec

/-- Explicit product decomposition by the packet kernel and coefficient
space. -/
def equivKernelProd :
    V ≃ₗ[K] (LinearMap.ker (evaluationMap pair s) × ((d : s) → K)) :=
  P.toSplitMap.equivKernelProd

/-- The packet kernel is complementary to the image of the chosen right
inverse. -/
theorem isCompl_kernel_range_rightInv :
    IsCompl (LinearMap.ker (evaluationMap pair s))
      (LinearMap.range P.rightInv) :=
  P.toSplitMap.isCompl_kernel_range_rightInv

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
      (LinearMap.range S.rightInv) := by
  rw [P.annihilator_eq_ker_evaluation]
  exact S.isCompl_kernel_range_rightInv

/-- Linear independence of the finite trace packet is sufficient to produce a
complementary persistent-kernel direction. -/
theorem exists_complement_of_linearIndependent
    (hli : LinearIndependent K (fun d : P.packet => pair d.1)) :
    ∃ Q : Submodule K V,
      IsCompl
        (NoetherianOperatorOrbit.annihilatorVia pair
          (NoetherianOperatorOrbit.orbitModule ops seed)) Q := by
  rcases exists_splitPacket_of_linearIndependent pair P.packet hli with ⟨S⟩
  exact ⟨LinearMap.range S.rightInv, P.persistentKernel_isCompl S⟩

end OrbitPacket

end Orbit

end

end FiniteKernelCentre
end PCRLean
