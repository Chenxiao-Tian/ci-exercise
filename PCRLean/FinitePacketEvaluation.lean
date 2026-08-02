import Mathlib
import PCRLean.SplitKernelCentre

/-!
# Finite Hasse--Cartier packet evaluation

A finite family of linear trace functionals determines one evaluation map.  Its
kernel is exactly the persistent direction kernel cut out by every member of
the packet.  When the evaluation map is split on a constant-rank chart, the
kernel becomes an explicit direct summand through `SplitKernelCentre`.

This file is the finite linear bridge between operator-orbit packetization and
regular-core extraction.  Constancy of rank and geometric integration into an
ambient coherent ideal remain separate geometric theorems.
-/

namespace PCRLean
namespace FinitePacketEvaluation

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Fintype ι]

abbrev Dual := Module.Dual K V

/-- Evaluate every functional in one finite packet. -/
def evalMap (packet : ι → Dual (K := K) (V := V)) : V →ₗ[K] (ι → K) where
  toFun x i := packet i x
  map_add' x y := by
    funext i
    exact map_add (packet i) x y
  map_smul' a x := by
    funext i
    exact map_smul (packet i) a x

/-- The persistent direction kernel of the finite packet. -/
def persistentKernel (packet : ι → Dual (K := K) (V := V)) : Submodule K V :=
  LinearMap.ker (evalMap packet)

/-- Membership in the persistent kernel is simultaneous vanishing of every
packet functional. -/
theorem mem_persistentKernel_iff
    (packet : ι → Dual (K := K) (V := V)) (x : V) :
    x ∈ persistentKernel packet ↔ ∀ i, packet i x = 0 := by
  rw [persistentKernel, LinearMap.mem_ker]
  constructor
  · intro hx i
    exact congrFun hx i
  · intro hx
    funext i
    exact hx i

/-- Adding a packet functional can only shrink the persistent kernel. -/
theorem persistentKernel_antitone
    {packet₁ packet₂ : ι → Dual (K := K) (V := V)}
    (h : ∀ i x, packet₂ i x = 0 → packet₁ i x = 0) :
    persistentKernel packet₂ ≤ persistentKernel packet₁ := by
  intro x hx
  rw [mem_persistentKernel_iff] at hx ⊢
  intro i
  exact h i x (hx i)

/-- An explicit section of the finite evaluation map packages the packet as a
split surjection. -/
def splitSurjection
    (packet : ι → Dual (K := K) (V := V))
    (section : (ι → K) →ₗ[K] V)
    (hsection : (evalMap packet).comp section = LinearMap.id) :
    SplitKernelCentre.SplitSurjection (R := K) (V := V) (W := ι → K) where
  map := evalMap packet
  section := section
  rightInverse := hsection

/-- On a chart carrying a section, the persistent kernel is an explicit direct
summand of the direction module. -/
theorem kernel_complemented_of_section
    (packet : ι → Dual (K := K) (V := V))
    (section : (ι → K) →ₗ[K] V)
    (hsection : (evalMap packet).comp section = LinearMap.id) :
    ∃ e : V ≃ₗ[K] persistentKernel packet × (ι → K),
      ∀ x, (e x).1.1 = x - section (evalMap packet x) := by
  let S := splitSurjection packet section hsection
  simpa [persistentKernel, S, splitSurjection] using S.kernel_is_complemented

/-- The finite packet map is injective on the chosen trace section. -/
theorem section_injective
    (packet : ι → Dual (K := K) (V := V))
    (section : (ι → K) →ₗ[K] V)
    (hsection : (evalMap packet).comp section = LinearMap.id) :
    Function.Injective section := by
  intro a b hab
  have h := congrArg (evalMap packet) hab
  have ha : evalMap packet (section a) = a := by
    have := LinearMap.congr_fun hsection a
    simpa using this
  have hb : evalMap packet (section b) = b := by
    have := LinearMap.congr_fun hsection b
    simpa using this
  simpa [ha, hb] using h

end

end FinitePacketEvaluation
end PCRLean
