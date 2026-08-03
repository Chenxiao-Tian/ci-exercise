import Mathlib
import PCRLean.FinitePacketEvaluation

/-!
# Biorthogonal finite packets

An invertible minor of a finite Hasse--Cartier packet provides explicit test
vectors biorthogonal to the packet rows.  Their finite linear combination is a
right inverse of the packet evaluation map, hence the persistent kernel is a
direct summand.  This is the coordinate-free algebra behind constant-rank
charts.
-/

namespace PCRLean
namespace BiorthogonalPacket

noncomputable section

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual K V

/-- A packet of functionals with chosen biorthogonal vectors. -/
structure Frame where
  functional : ι → Dual (K := K) (V := V)
  vector : ι → V
  biorthogonal : ∀ i j, functional i (vector j) = if i = j then 1 else 0

namespace Frame

variable (F : Frame (K := K) (V := V) (ι := ι))

/-- The explicit right inverse assembled from the biorthogonal vectors. -/
def section : (ι → K) →ₗ[K] V where
  toFun a := ∑ j : ι, a j • F.vector j
  map_add' a b := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [mul_smul, Finset.smul_sum]

/-- Evaluating one packet row on the explicit section returns the corresponding
coordinate. -/
theorem functional_section (a : ι → K) (i : ι) :
    F.functional i (F.section a) = a i := by
  rw [section]
  simp only [map_sum, map_smul, F.biorthogonal]
  classical
  simp

/-- The section is a genuine right inverse of the finite evaluation map. -/
theorem rightInverse :
    (FinitePacketEvaluation.evalMap F.functional).comp F.section = LinearMap.id := by
  ext a i
  exact F.functional_section a i

/-- The packet evaluation map is split surjective. -/
def splitSurjection :
    SplitKernelCentre.SplitSurjection (R := K) (V := V) (W := ι → K) :=
  FinitePacketEvaluation.splitSurjection
    F.functional F.section F.rightInverse

/-- The packet's persistent kernel is an explicit direct summand. -/
theorem kernel_complemented :
    ∃ e : V ≃ₗ[K]
        FinitePacketEvaluation.persistentKernel F.functional × (ι → K),
      ∀ x, (e x).1.1 =
        x - F.section (FinitePacketEvaluation.evalMap F.functional x) := by
  exact FinitePacketEvaluation.kernel_complemented_of_section
    F.functional F.section F.rightInverse

/-- The packet rows are linearly independent. -/
theorem functional_linearIndependent :
    LinearIndependent K F.functional := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun f : Dual (K := K) (V := V) => f (F.vector i)) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, F.biorthogonal] at h
  classical
  simpa using h

/-- The chosen packet vectors are linearly independent. -/
theorem vector_linearIndependent :
    LinearIndependent K F.vector := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (F.functional i) hc
  simp only [map_sum, map_smul, F.biorthogonal] at h
  classical
  simpa using h

end Frame

end

end BiorthogonalPacket
end PCRLean
