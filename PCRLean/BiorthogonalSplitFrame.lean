import Mathlib
import PCRLean.SplitConormalFrame

/-!
# Biorthogonal split conormal frames

A finite conormal packet is split as soon as one can exhibit transverse vectors
biorthogonal to the packet. The explicit section sends a coefficient vector to
the corresponding linear combination of transverse vectors. Biorthogonality
makes this section a right inverse of evaluation, hence the persistent kernel
is a direct summand.

Every proof here is valid over an arbitrary commutative ring. In geometry, an
invertible Jacobian minor supplies the biorthogonal transverse vectors after
localization; the Fitting ideal of those minors records exactly where the
certificate fails.
-/

namespace PCRLean
namespace BiorthogonalSplitFrame

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual K V

/-- Finite packet of functionals together with biorthogonal transverse
vectors. -/
structure Frame where
  packet : ι → Dual (K := K) (V := V)
  transverse : ι → V
  biorthogonal : ∀ i j,
    packet i (transverse j) = if i = j then 1 else 0

namespace Frame

variable (F : Frame (K := K) (V := V) (ι := ι))

/-- Evaluation by the conormal packet. -/
def eval : V →ₗ[K] (ι → K) where
  toFun x i := F.packet i x
  map_add' := by
    intro x y
    funext i
    simp
  map_smul' := by
    intro a x
    funext i
    simp

/-- Explicit transverse section. -/
def section : (ι → K) →ₗ[K] V where
  toFun a := ∑ j : ι, a j • F.transverse j
  map_add' := by
    intro a b
    simp_rw [add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c a
    simp_rw [Pi.smul_apply, smul_smul]
    rw [Finset.smul_sum]

/-- Evaluation of the section is the identity. -/
theorem eval_section (a : ι → K) :
    F.eval (F.section a) = a := by
  funext i
  simp only [eval, section, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, LinearMap.map_smul_of_tower, Pi.zero_apply]
  calc
    ∑ j : ι, a j * F.packet i (F.transverse j) =
        ∑ j : ι, if i = j then a j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [F.biorthogonal i j]
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    _ = a i := by simp

/-- Linear-map form of the right-inverse identity. -/
theorem rightInverse : F.eval.comp F.section = LinearMap.id := by
  ext a i
  exact congrFun (F.eval_section a) i

/-- The associated split conormal frame. -/
def splitFrame :
    SplitConormalFrame.Frame (K := K) (V := V) (ι := ι) where
  eval := F.eval
  split := F.section
  rightInverse := F.rightInverse

/-- The common kernel of the packet is complemented by the transverse span. -/
theorem kernel_isCompl_transverseRange :
    IsCompl (LinearMap.ker F.eval) (LinearMap.range F.section) :=
  F.splitFrame.isCompl_ker_range

/-- The packet is linearly independent. -/
theorem packet_linearIndependent :
    LinearIndependent K F.packet := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have happly := congrArg
    (fun f : Dual (K := K) (V := V) => f (F.transverse i)) hg
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    F.biorthogonal] at happly
  simpa using happly

/-- The transverse vectors are linearly independent. -/
theorem transverse_linearIndependent :
    LinearIndependent K F.transverse := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have happly := congrArg (F.packet i) hg
  simp only [map_sum, map_smul, F.biorthogonal] at happly
  simpa using happly

end Frame

end

end BiorthogonalSplitFrame
end PCRLean
