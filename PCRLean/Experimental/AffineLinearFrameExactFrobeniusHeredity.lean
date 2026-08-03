import Mathlib
import PCRLean.LinearCoordinateChange
import PCRLean.CoordinateCentreProper
import PCRLean.Experimental.AffineCoordinateSubspaceHeredity
import PCRLean.Experimental.LinearFrameSubspaceHeredity
import PCRLean.Experimental.CoordinateCentreExactFrobeniusHeredity

/-!
# Exact Frobenius heredity for affine linear centres

The exact coordinate-centre reflection theorem is stable under two geometric
changes of variables:

* translation in the normal coordinates, producing an affine coordinate
  subspace; and
* an arbitrary full linear frame, producing an arbitrary split affine linear
  regular centre.

For every such centre ideal `I`, every prime power `q = p^e`, every mark `m`
and every polynomial `g`, the file proves

`g^q ∈ I^(q*m) ↔ g ∈ I^m`.

Thus scaled Frobenius compression preserves the marked singular condition not
only at points, but along every globally framed affine linear regular centre.
Local frame descent, nonlinear regular immersions, passive owners, boundaries
and controlled transforms remain open.
-/

namespace PCRLean
namespace Experimental
namespace AffineLinearFrameExactFrobeniusHeredity

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

/-- Exact reflection along an affine coordinate subspace. -/
theorem frobeniusPower_mem_affineCentreIdeal_pow_iff
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (b : ι → K)
    (g : P (K := K) (α := α) (ι := ι)) :
    g ^ (p ^ e) ∈
        (AffineCoordinateSubspaceHeredity.affineCentreIdeal
          (α := α) b) ^ ((p ^ e) * mark) ↔
      g ∈ (AffineCoordinateSubspaceHeredity.affineCentreIdeal
          (α := α) b) ^ mark := by
  rw [AffineCoordinateSubspaceHeredity.mem_affineCentreIdeal_pow_iff,
    AffineCoordinateSubspaceHeredity.mem_affineCentreIdeal_pow_iff,
    map_pow]
  exact
    CoordinateCentreExactFrobeniusHeredity.frobeniusPower_mem_centreIdeal_pow_iff
      p e mark (AffineCoordinateSubspaceHeredity.normalTranslate
        (α := α) b g)

/-- The affine coordinate-centre ideal is proper. -/
theorem affineCentreIdeal_ne_top (b : ι → K) :
    AffineCoordinateSubspaceHeredity.affineCentreIdeal
      (α := α) b ≠ ⊤ := by
  intro htop
  have hunit : (1 : P (K := K) (α := α) (ι := ι)) ∈
      AffineCoordinateSubspaceHeredity.affineCentreIdeal
        (α := α) b := by
    rw [htop]
    trivial
  have hm := Ideal.mem_map_of_mem
    (AffineCoordinateSubspaceHeredity.normalTranslate (α := α) b) hunit
  rw [AffineCoordinateSubspaceHeredity.map_affineCentreIdeal_eq_centreIdeal]
    at hm
  apply CoordinateCentreProper.centreIdeal_ne_top
    (K := K) (α := α) (ι := ι)
  exact Ideal.eq_top_iff_one.mpr (by simpa using hm)

/-- Exact reflection along a linearly transported centre through the origin. -/
theorem frobeniusPower_mem_frameCentreIdeal_pow_iff
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι)) :
    g ^ (p ^ e) ∈
        (LinearFrameSubspaceHeredity.frameCentreIdeal F) ^
          ((p ^ e) * mark) ↔
      g ∈ (LinearFrameSubspaceHeredity.frameCentreIdeal F) ^ mark := by
  rw [LinearFrameSubspaceHeredity.mem_frameCentreIdeal_pow_iff,
    LinearFrameSubspaceHeredity.mem_frameCentreIdeal_pow_iff,
    map_pow]
  exact
    CoordinateCentreExactFrobeniusHeredity.frobeniusPower_mem_centreIdeal_pow_iff
      p e mark (F.inverse g)

/-- One affine normal equation after a full linear frame. -/
def affineFrameCentreGenerator
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) (i : ι) :
    P (K := K) (α := α) (ι := ι) :=
  F.forward
    (AffineCoordinateSubspaceHeredity.affineCentreGenerator
      (α := α) b i)

/-- Actual ideal of a globally framed affine linear centre. -/
def affineFrameCentreIdeal
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    Ideal (P (K := K) (α := α) (ι := ι)) :=
  Ideal.span (Set.range (affineFrameCentreGenerator F b))

/-- Each framed affine equation belongs to the actual centre ideal. -/
theorem affineFrameCentreGenerator_mem
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) (i : ι) :
    affineFrameCentreGenerator F b i ∈
      affineFrameCentreIdeal F b :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Forward frame transport of the affine coordinate ideal. -/
theorem map_affineCentreIdeal_eq_affineFrameCentreIdeal
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    Ideal.map F.forward
        (AffineCoordinateSubspaceHeredity.affineCentreIdeal
          (α := α) b) =
      affineFrameCentreIdeal F b := by
  apply le_antisymm
  · rw [AffineCoordinateSubspaceHeredity.affineCentreIdeal,
      affineFrameCentreIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    exact affineFrameCentreGenerator_mem F b i
  · rw [affineFrameCentreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact Ideal.mem_map_of_mem F.forward
      (AffineCoordinateSubspaceHeredity.affineCentreGenerator_mem
        (α := α) b i)

/-- Inverse frame transport of the affine linear centre ideal. -/
theorem map_affineFrameCentreIdeal_eq_affineCentreIdeal
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    Ideal.map F.inverse (affineFrameCentreIdeal F b) =
      AffineCoordinateSubspaceHeredity.affineCentreIdeal
        (α := α) b := by
  apply le_antisymm
  · rw [affineFrameCentreIdeal,
      AffineCoordinateSubspaceHeredity.affineCentreIdeal,
      Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) =>
        H (AffineCoordinateSubspaceHeredity.affineCentreGenerator
          (α := α) b i))
      F.inverse_comp_forward
    simpa [affineFrameCentreGenerator, AlgHom.comp_apply] using
      hcomp ▸ AffineCoordinateSubspaceHeredity.affineCentreGenerator_mem
        (α := α) b i
  · rw [AffineCoordinateSubspaceHeredity.affineCentreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem F.inverse
      (affineFrameCentreGenerator_mem F b i)
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) =>
        H (AffineCoordinateSubspaceHeredity.affineCentreGenerator
          (α := α) b i))
      F.inverse_comp_forward
    simpa [affineFrameCentreGenerator, AlgHom.comp_apply] using hcomp ▸ hm

/-- Exact power-membership transport for a framed affine centre. -/
theorem mem_affineFrameCentreIdeal_pow_iff
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K)
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ (affineFrameCentreIdeal F b) ^ mark ↔
      F.inverse f ∈
        (AffineCoordinateSubspaceHeredity.affineCentreIdeal
          (α := α) b) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem F.inverse hf
    rw [Ideal.map_pow, map_affineFrameCentreIdeal_eq_affineCentreIdeal]
      at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem F.forward hf
    rw [Ideal.map_pow, map_affineCentreIdeal_eq_affineFrameCentreIdeal]
      at hm
    have hcomp := congrArg
      (fun H : P (K := K) (α := α) (ι := ι) →ₐ[K]
          P (K := K) (α := α) (ι := ι) => H f)
      F.forward_comp_inverse
    simpa [AlgHom.comp_apply] using hcomp ▸ hm

/-- The framed affine centre ideal is finite type. -/
theorem affineFrameCentreIdeal_fg
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    (affineFrameCentreIdeal F b).FG := by
  rw [affineFrameCentreIdeal]
  exact Submodule.fg_span (Set.finite_range (affineFrameCentreGenerator F b))

/-- The framed affine centre ideal is proper. -/
theorem affineFrameCentreIdeal_ne_top
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    affineFrameCentreIdeal F b ≠ ⊤ := by
  intro htop
  have hunit : (1 : P (K := K) (α := α) (ι := ι)) ∈
      affineFrameCentreIdeal F b := by
    rw [htop]
    trivial
  have hm := Ideal.mem_map_of_mem F.inverse hunit
  rw [map_affineFrameCentreIdeal_eq_affineCentreIdeal] at hm
  apply affineCentreIdeal_ne_top (α := α) b
  exact Ideal.eq_top_iff_one.mpr (by simpa using hm)

/-- Main exact theorem for an arbitrary globally framed affine linear centre. -/
theorem frobeniusPower_mem_affineFrameCentreIdeal_pow_iff
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat) (b : ι → K)
    (g : P (K := K) (α := α) (ι := ι)) :
    g ^ (p ^ e) ∈
        (affineFrameCentreIdeal F b) ^ ((p ^ e) * mark) ↔
      g ∈ (affineFrameCentreIdeal F b) ^ mark := by
  rw [mem_affineFrameCentreIdeal_pow_iff,
    mem_affineFrameCentreIdeal_pow_iff, map_pow]
  exact frobeniusPower_mem_affineCentreIdeal_pow_iff
    p e mark b (F.inverse g)

end

end AffineLinearFrameExactFrobeniusHeredity
end Experimental
end PCRLean
