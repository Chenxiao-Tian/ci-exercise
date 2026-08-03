import Mathlib
import PCRLean.NoetherianOperatorOrbit
import PCRLean.OperatorOrbitEquivFixed

/-!
# Presentation invariance of persistent operator kernels

Equivalent operator presentations and compatible tangent-coordinate changes
carry the persistent Hasse--Cartier annihilator kernel exactly to one another.
This removes the finite-generator choice from the linearized construction.

The geometric task is to obtain the required equivalences from changes of
marked/Rees presentation and smooth or etale pullback.
-/

namespace PCRLean
namespace PersistentKernelEquiv

noncomputable section

universe u v w x y

variable {R : Type u}
variable {D : Type v} {D' : Type w}
variable {V : Type x} {V' : Type y}
variable {ι : Type*}
variable [CommSemiring R]
variable [AddCommMonoid D] [Module R D]
variable [AddCommMonoid D'] [Module R D']
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid V'] [Module R V']

abbrev DualV := Module.Dual R V
abbrev DualV' := Module.Dual R V'

/-- Compatibility of two pairings with changes of packet and tangent
presentation. -/
def PairingCompatible
    (eD : D ≃ₗ[R] D') (eV : V ≃ₗ[R] V')
    (pair : D →ₗ[R] DualV (R := R) (V := V))
    (pair' : D' →ₗ[R] DualV' (R := R) (V := V')) : Prop :=
  ∀ d x, pair' (eD d) (eV x) = pair d x

/-- Membership in the persistent annihilator is invariant under compatible
operator and tangent equivalences. -/
theorem mem_persistentKernel_iff
    (eD : D ≃ₗ[R] D') (eV : V ≃ₗ[R] V')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (hop : OperatorOrbitEquivFixed.Intertwines eD ops ops')
    (seed : D)
    (pair : D →ₗ[R] DualV (R := R) (V := V))
    (pair' : D' →ₗ[R] DualV' (R := R) (V := V'))
    (hpair : PairingCompatible eD eV pair pair')
    (x : V) :
    x ∈ NoetherianOperatorOrbit.annihilatorVia pair
        (NoetherianOperatorOrbit.orbitModule ops seed) ↔
      eV x ∈ NoetherianOperatorOrbit.annihilatorVia pair'
        (NoetherianOperatorOrbit.orbitModule ops' (eD seed)) := by
  have horbit := OperatorOrbitEquivFixed.map_orbitModule_eq
    eD ops ops' hop seed
  constructor
  · intro hx
    rw [NoetherianOperatorOrbit.mem_annihilatorVia_iff]
    intro d' hd'
    rw [← horbit] at hd'
    rcases hd' with ⟨d, hd, rfl⟩
    rw [hpair]
    exact hx d hd
  · intro hx
    rw [NoetherianOperatorOrbit.mem_annihilatorVia_iff]
    intro d hd
    have hmap : eD d ∈
        (NoetherianOperatorOrbit.orbitModule ops seed).map eD.toLinearMap :=
      ⟨d, hd, rfl⟩
    rw [horbit] at hmap
    have hz := hx (eD d) hmap
    rw [hpair] at hz
    exact hz

/-- The linear equivalence maps the entire persistent kernel submodule onto the
persistent kernel in the new presentation. -/
theorem map_persistentKernel_eq
    (eD : D ≃ₗ[R] D') (eV : V ≃ₗ[R] V')
    (ops : ι → Module.End R D) (ops' : ι → Module.End R D')
    (hop : OperatorOrbitEquivFixed.Intertwines eD ops ops')
    (seed : D)
    (pair : D →ₗ[R] DualV (R := R) (V := V))
    (pair' : D' →ₗ[R] DualV' (R := R) (V := V'))
    (hpair : PairingCompatible eD eV pair pair') :
    (NoetherianOperatorOrbit.annihilatorVia pair
      (NoetherianOperatorOrbit.orbitModule ops seed)).map eV.toLinearMap =
      NoetherianOperatorOrbit.annihilatorVia pair'
        (NoetherianOperatorOrbit.orbitModule ops' (eD seed)) := by
  ext x'
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_persistentKernel_iff eD eV ops ops' hop seed pair pair' hpair x).mp hx
  · intro hx'
    refine ⟨eV.symm x', ?_, by simp⟩
    have h := (mem_persistentKernel_iff eD eV ops ops' hop seed pair pair'
      hpair (eV.symm x')).mpr ?_
    · exact h
    · simpa using hx'

end

end PersistentKernelEquiv
end PCRLean
