import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.CoordinateBlowupChart
import PCRLean.CoordinateKernelIdeal

/-!
# The coordinate centre as an actual retraction kernel

The passive-coordinate retraction keeps the `α` variables and kills every
centre variable indexed by `ι`. Its kernel is exactly the coordinate centre
ideal. This identifies the quotient by the centre with the passive polynomial
ring.
-/

namespace PCRLean
namespace CoordinateCentreKernelBridge

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {α : Type v} {ι : Type w}

abbrev A := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

/-- Inclusion of passive variables into the full variable set. -/
def passiveEmbedding : α → α ⊕ ι := Sum.inl

theorem passiveEmbedding_injective :
    Function.Injective (passiveEmbedding (α := α) (ι := ι)) := by
  intro a b h
  exact Sum.inl.inj h

/-- Kernel of the retraction which kills all centre variables. -/
def passiveKernel : Ideal (A (K := K) (α := α) (ι := ι)) :=
  CoordinateKernelIdeal.ideal (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

/-- Every coordinate centre generator is killed by the passive retraction. -/
theorem centreIdeal_le_passiveKernel :
    CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) ≤
      passiveKernel (K := K) (α := α) (ι := ι) := by
  rw [CoordinateBlowupChart.centreIdeal, Ideal.span_le]
  rintro x ⟨i, rfl⟩
  apply RingHom.mem_ker.mpr
  simp [passiveKernel, CoordinateKernelIdeal.ideal,
    CoordinateKernelIdeal.retract, passiveEmbedding,
    CoordinateBlowupChart.centreVar]

/-- The coordinate centre is exactly the kernel of the passive retraction. -/
theorem centreIdeal_eq_passiveKernel :
    CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) =
      passiveKernel (K := K) (α := α) (ι := ι) := by
  apply le_antisymm
  · exact centreIdeal_le_passiveKernel (K := K) (α := α) (ι := ι)
  · intro f hf
    have hzero :
        CoordinateKernelIdeal.retract (R := K)
          (passiveEmbedding (α := α) (ι := ι))
          (passiveEmbedding_injective (α := α) (ι := ι)) f = 0 := by
      exact RingHom.mem_ker.mp hf
    rw [CoordinateBlowupChart.centreIdeal]
    have hgenerators :
        Set.range
            (CoordinateBlowupChart.centreVar
              (R := K) (α := α) (ι := ι)) =
          MvPolynomial.X '' Set.range (Sum.inr : ι → α ⊕ ι) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Sum.inr i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨s, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hgenerators, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hnone
    push_neg at hnone
    have hsupp : (m.support : Set (α ⊕ ι)) ⊆ Set.range Sum.inl := by
      intro s hs
      cases s with
      | inl a => exact ⟨a, rfl⟩
      | inr i =>
          exfalso
          have hmi : m (Sum.inr i) ≠ 0 :=
            Finsupp.mem_support_iff.mp hs
          exact hmi (hnone (Sum.inr i) ⟨i, rfl⟩)
    let d : α →₀ Nat :=
      m.comapDomain Sum.inl
        (passiveEmbedding_injective (α := α) (ι := ι)).injOn
    have hmd : d.mapDomain Sum.inl = m := by
      simpa [d] using
        (m.mapDomain_comapDomain Sum.inl
          (passiveEmbedding_injective (α := α) (ι := ι)) hsupp)
    have hcoeff : f.coeff (d.mapDomain Sum.inl) = 0 := by
      have hz := congrArg (fun g : MvPolynomial α K => g.coeff d) hzero
      simpa [CoordinateKernelIdeal.retract,
        MvPolynomial.coeff_killCompl] using hz
    rw [hmd] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

/-- Explicit quotient by the actual coordinate centre. -/
noncomputable def quotientEquiv :
    (A (K := K) (α := α) (ι := ι) ⧸
        CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ≃+*
      MvPolynomial α K := by
  rw [centreIdeal_eq_passiveKernel (K := K) (α := α) (ι := ι)]
  exact CoordinateKernelIdeal.quotientEquiv (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

/-- The centre is proper over a nontrivial coefficient ring. -/
theorem centreIdeal_ne_top [Nontrivial K] :
    CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι) ≠ ⊤ := by
  rw [centreIdeal_eq_passiveKernel (K := K) (α := α) (ι := ι)]
  exact CoordinateKernelIdeal.ideal_ne_top (R := K)
    (passiveEmbedding (α := α) (ι := ι))
    (passiveEmbedding_injective (α := α) (ι := ι))

end

end CoordinateCentreKernelBridge
end PCRLean
