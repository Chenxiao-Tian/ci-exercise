import Mathlib
import PCRLean.LinearCoordinateChange
import PCRLean.CoordinateCentreProper
import PCRLean.Experimental.CoordinateSubspaceOrderHeredity

/-!
# Linear-frame positive-dimensional centre heredity

A full dual frame gives a polynomial algebra automorphism.  Transporting the
standard coordinate centre through this automorphism produces an actual ideal
cut out by independent linear forms.  The inverse frame carries every power of
that ideal exactly back to the corresponding power of the standard coordinate
centre.

Define normal order for the transported centre by applying the inverse frame
and measuring centre degree there.  Frobenius prime powers commute with the
frame homomorphism, so root compression preserves this order exactly after
scaling the mark.  Thus a root order certificate yields actual marked-power
containment along an arbitrary split linear regular centre, not merely a
coordinate or rational-point centre.

The theorem remains affine and globally framed.  Local frame existence,
overlap descent, nonlinear regular centres, passive Tor safety, boundary SNC
and hereditary blowup transforms remain separate.
-/

namespace PCRLean
namespace Experimental
namespace LinearFrameSubspaceHeredity

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]

abbrev Variables := α ⊕ ι
abbrev P := MvPolynomial (Variables (α := α) (ι := ι)) K

open CoordinateSubspaceOrderHeredity

variable (F : LinearCoordinateChange.FullFrame
  (K := K) (σ := Variables (α := α) (ι := ι)))

/-- One transported normal linear equation. -/
def frameCentreGenerator (i : ι) :
    P (K := K) (α := α) (ι := ι) :=
  F.forward
    (CoordinateBlowupChart.centreVar
      (R := K) (α := α) (ι := ι) i)

/-- Actual ideal of the transported linear centre. -/
def frameCentreIdeal :
    Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.span (Set.range F.frameCentreGenerator)

/-- Each transported normal equation belongs to the actual centre ideal. -/
theorem frameCentreGenerator_mem (i : ι) :
    F.frameCentreGenerator i ∈ F.frameCentreIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

/-- The forward frame sends the standard coordinate centre ideal exactly to
the transported linear centre ideal. -/
theorem map_centreIdeal_eq_frameCentreIdeal :
    Ideal.map F.forward
        (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) =
      F.frameCentreIdeal := by
  apply le_antisymm
  · rw [CoordinateBlowupChart.centreIdeal, frameCentreIdeal,
      Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    exact frameCentreGenerator_mem F i
  · rw [frameCentreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem F.forward
      (CoordinateSubspaceOrderHeredity.centreVar_mem
        (K := K) (α := α) i)

/-- The inverse frame sends the transported centre ideal back to the standard
coordinate centre ideal. -/
theorem map_frameCentreIdeal_eq_centreIdeal :
    Ideal.map F.inverse F.frameCentreIdeal =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) := by
  apply le_antisymm
  · rw [frameCentreIdeal, CoordinateBlowupChart.centreIdeal,
      Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) =>
        H (CoordinateBlowupChart.centreVar
          (R := K) (α := α) (ι := ι) i))
      F.inverse_comp_forward
    simpa [frameCentreGenerator, AlgHom.comp_apply] using
      hcomp ▸ CoordinateSubspaceOrderHeredity.centreVar_mem
        (K := K) (α := α) i
  · rw [CoordinateBlowupChart.centreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem F.inverse
      (frameCentreGenerator_mem F i)
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) =>
        H (CoordinateBlowupChart.centreVar
          (R := K) (α := α) (ι := ι) i))
      F.inverse_comp_forward
    simpa [frameCentreGenerator, AlgHom.comp_apply] using hcomp ▸ hm

/-- The forward frame transports every power of the coordinate centre. -/
theorem map_centreIdeal_pow_eq_frameCentreIdeal_pow (mark : Nat) :
    Ideal.map F.forward
        ((CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark) =
      F.frameCentreIdeal ^ mark := by
  rw [Ideal.map_pow, F.map_centreIdeal_eq_frameCentreIdeal]

/-- The inverse frame transports every power of the linear centre back to the
coordinate model. -/
theorem map_frameCentreIdeal_pow_eq_centreIdeal_pow (mark : Nat) :
    Ideal.map F.inverse (F.frameCentreIdeal ^ mark) =
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) ^ mark := by
  rw [Ideal.map_pow, F.map_frameCentreIdeal_eq_centreIdeal]

/-- Exact power-membership transport through the frame. -/
theorem mem_frameCentreIdeal_pow_iff
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ F.frameCentreIdeal ^ mark ↔
      F.inverse f ∈
        (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem F.inverse hf
    rw [F.map_frameCentreIdeal_pow_eq_centreIdeal_pow] at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem F.forward hf
    rw [F.map_centreIdeal_pow_eq_frameCentreIdeal_pow] at hm
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) => H f)
      F.forward_comp_inverse
    simpa [AlgHom.comp_apply] using hcomp ▸ hm

/-- The transported centre ideal is finitely generated by its finite normal
frame. -/
theorem frameCentreIdeal_fg : F.frameCentreIdeal.FG := by
  rw [frameCentreIdeal]
  exact Submodule.fg_span (Set.finite_range F.frameCentreGenerator)

/-- The transported centre ideal is proper. -/
theorem frameCentreIdeal_ne_top : F.frameCentreIdeal ≠ ⊤ := by
  intro htop
  have hunit : (1 : P (K := K) (α := α) (ι := ι)) ∈
      F.frameCentreIdeal := by
    rw [htop]
    trivial
  have hm := Ideal.mem_map_of_mem F.inverse hunit
  rw [F.map_frameCentreIdeal_eq_centreIdeal] at hm
  apply CoordinateCentreProper.centreIdeal_ne_top
    (K := K) (α := α) (ι := ι)
  exact Ideal.eq_top_iff_one.mpr (by simpa using hm)

/-- Normal order along the transported linear centre. -/
def FrameCentreOrderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) : Prop :=
  CoordinateSubspaceOrderHeredity.CentreOrderGE (F.inverse f) mark

/-- Frame-centre order gives actual marked-power containment. -/
theorem mem_frameCentreIdeal_pow_of_orderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat)
    (horder : F.FrameCentreOrderGE f mark) :
    f ∈ F.frameCentreIdeal ^ mark := by
  apply (F.mem_frameCentreIdeal_pow_iff f mark).mpr
  exact CoordinateSubspaceOrderHeredity.mem_centreIdeal_pow_of_centreOrderGE
    (F.inverse f) mark horder

/-- Frobenius mark compression preserves order along an arbitrary transported
linear centre. -/
theorem frameCentreOrderGE_power_iff
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι)) :
    F.FrameCentreOrderGE (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      F.FrameCentreOrderGE g mark := by
  unfold FrameCentreOrderGE
  rw [map_pow]
  exact CoordinateSubspaceOrderHeredity.centreOrderGE_power_iff
    p e mark (F.inverse g)

/-- A root order certificate produces marked permissibility for its
prime-power equation along the transported actual linear centre. -/
theorem frobeniusPower_mem_frameCentreIdeal_pow
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι))
    (hrootOrder : F.FrameCentreOrderGE g mark) :
    g ^ (p ^ e) ∈ F.frameCentreIdeal ^ ((p ^ e) * mark) := by
  apply F.mem_frameCentreIdeal_pow_of_orderGE
  exact (F.frameCentreOrderGE_power_iff p e mark g).mpr hrootOrder

end

end LinearFrameSubspaceHeredity
end Experimental
end PCRLean
