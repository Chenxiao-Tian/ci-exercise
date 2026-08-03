import Mathlib
import PCRLean.NoetherianOperatorOrbit
import PCRLean.SplitConormalFrame

/-!
# Linearized geometric realization of a finite operator packet

A Noetherian Hasse--Cartier orbit yields a finite packet of functionals. If the
finite evaluation map has an explicit splitting, its persistent annihilator is
a split direct summand of the ambient tangent module. This is the exact
linearized regular-centre theorem.

The remaining geometric bridge is to produce the splitting Zariski-locally
from an intrinsic packet and to integrate the split conormal frame to actual
functions defining a regular permissible centre.
-/

namespace PCRLean
namespace LinearizedGeometricRealization

noncomputable section

universe u v w x

variable {K : Type u} {D : Type v} {V : Type w} {ι : Type x}
variable [Field K]
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V]

abbrev DualV := Module.Dual K V

/-- Evaluation by a finite packet of trace elements. -/
def packetEval
    (pair : D →ₗ[K] DualV (K := K) (V := V)) (s : Finset D) :
    V →ₗ[K] (↥s → K) where
  toFun := fun x d => pair d.1 x
  map_add' := by
    intro x y
    funext d
    simp
  map_smul' := by
    intro a x
    funext d
    simp

/-- A finite orbit packet together with an explicit transverse splitting. -/
structure Certificate
    (ops : ι → Module.End K D) (seed : D)
    (pair : D →ₗ[K] DualV (K := K) (V := V)) where
  packet : Finset D
  packet_in_orbit :
    (packet : Set D) ⊆ NoetherianOperatorOrbit.orbitSet ops seed
  packet_spans :
    NoetherianOperatorOrbit.orbitModule ops seed =
      Submodule.span K (packet : Set D)
  split : (↥packet → K) →ₗ[K] V
  rightInverse :
    (packetEval pair packet).comp split = LinearMap.id

namespace Certificate

variable {ops : ι → Module.End K D} {seed : D}
    {pair : D →ₗ[K] DualV (K := K) (V := V)}
    (C : Certificate ops seed pair)

/-- The split conormal frame carried by the finite packet. -/
def splitFrame :
    SplitConormalFrame.Frame (K := K) (V := V) (ι := ↥C.packet) where
  eval := packetEval pair C.packet
  split := C.split
  rightInverse := C.rightInverse

/-- Vanishing of the packet evaluation is exactly vanishing of every packet
functional. -/
theorem packetEval_eq_zero_iff (x : V) :
    packetEval pair C.packet x = 0 ↔
      ∀ d ∈ C.packet, pair d x = 0 := by
  constructor
  · intro h d hd
    have hd' := congrFun h ⟨d, hd⟩
    simpa [packetEval] using hd'
  · intro h
    funext d
    exact h d.1 d.2

/-- The persistent annihilator of the full operator orbit equals the kernel of
the finite split evaluation map. -/
theorem persistentKernel_eq_evalKer :
    NoetherianOperatorOrbit.annihilatorVia pair
      (NoetherianOperatorOrbit.orbitModule ops seed) =
      LinearMap.ker (packetEval pair C.packet) := by
  ext x
  rw [NoetherianOperatorOrbit.mem_annihilatorVia_iff_of_span_eq
    pair (NoetherianOperatorOrbit.orbitModule ops seed) C.packet
    C.packet_spans x]
  rw [LinearMap.mem_ker, C.packetEval_eq_zero_iff]

/-- The persistent operator kernel is a split direct summand; this is the
linear regularity conclusion supplied by the splitting certificate. -/
theorem persistentKernel_isCompl :
    IsCompl
      (NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed))
      (LinearMap.range C.split) := by
  rw [C.persistentKernel_eq_evalKer]
  exact (C.splitFrame).isCompl_ker_range

/-- The persistent kernel and transverse packet directions span the ambient
module. -/
theorem persistentKernel_sup_range_eq_top :
    NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) ⊔
      LinearMap.range C.split = ⊤ :=
  C.persistentKernel_isCompl.sup_eq_top

/-- The persistent kernel has trivial intersection with the transverse packet
range. -/
theorem persistentKernel_disjoint_range :
    Disjoint
      (NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed))
      (LinearMap.range C.split) :=
  C.persistentKernel_isCompl.disjoint

end Certificate

end

end LinearizedGeometricRealization
end PCRLean
