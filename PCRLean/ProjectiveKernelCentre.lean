import Mathlib.Algebra.Module.Projective
import PCRLean.FiniteKernelCentre

/-!
# Surjective finite packets and projective kernel centres

For a finite coefficient packet the target of the evaluation map is a finite
free module. Hence a surjective packet evaluation automatically has a linear
right inverse. Combined with `FiniteKernelCentre`, this turns the persistent
kernel into a direct summand without choosing a right inverse as extra
geometric data.

The remaining geometric obligation is to prove surjectivity after restricting
to the correct constant-rank open stratum and then to descend the resulting
local direct summands to one coherent regular centre.
-/

namespace PCRLean
namespace ProjectiveKernelCentre

noncomputable section

universe u v w

variable {K : Type u} {D : Type v} {V : Type w}
variable [Field K]
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V]

open FiniteKernelCentre

abbrev DualV := Module.Dual K V

/-- A surjective finite evaluation packet admits a right inverse because its
finite function-space target is free, hence projective. -/
theorem exists_splitPacket_of_surjective
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D)
    (hsurj : Function.Surjective (evaluationMap pair s)) :
    Nonempty (SplitPacket pair s) := by
  have hrange : LinearMap.range (evaluationMap pair s) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rcases LinearMap.exists_rightInverse_of_surjective
      (evaluationMap pair s) hrange with ⟨rightInv, hrightInv⟩
  exact ⟨⟨rightInv, hrightInv⟩⟩

/-- A surjective finite packet therefore has a complementary kernel. -/
theorem exists_complement_of_surjective
    (pair : D →ₗ[K] DualV (K := K) (V := V))
    (s : Finset D)
    (hsurj : Function.Surjective (evaluationMap pair s)) :
    ∃ rightInv : ((d : s) → K) →ₗ[K] V,
      IsCompl (LinearMap.ker (evaluationMap pair s))
        (LinearMap.range rightInv) := by
  rcases exists_splitPacket_of_surjective pair s hsurj with ⟨P⟩
  exact ⟨P.rightInv, P.isCompl_kernel_range_rightInv⟩

section Orbit

variable {ι : Type*} [IsNoetherian K D]

/-- If the finite evaluation map attached to a Noetherian operator-orbit packet
is surjective, then the persistent infinite-orbit kernel is a direct summand. -/
theorem persistentKernel_isCompl_of_surjective
    {ops : ι → Module.End K D} {seed : D}
    {pair : D →ₗ[K] DualV (K := K) (V := V)}
    (P : OrbitPacket ops seed pair)
    (hsurj : Function.Surjective (evaluationMap pair P.packet)) :
    ∃ rightInv : ((d : P.packet) → K) →ₗ[K] V,
      IsCompl
        (NoetherianOperatorOrbit.annihilatorVia pair
          (NoetherianOperatorOrbit.orbitModule ops seed))
        (LinearMap.range rightInv) := by
  rcases exists_splitPacket_of_surjective pair P.packet hsurj with ⟨S⟩
  exact ⟨S.rightInv, P.persistentKernel_isCompl S⟩

end Orbit

end

end ProjectiveKernelCentre
end PCRLean
