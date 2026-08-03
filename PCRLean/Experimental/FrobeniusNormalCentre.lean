import Mathlib
import PCRLean.Experimental.CoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.AffineLinearFrameExactFrobeniusHeredity

/-!
# Frobenius-normal centre filtrations

For a centre ideal `I` in characteristic `p`, define reflection of the
prime-power filtration by

`x^(p^e) ∈ I^((p^e)*m) → x ∈ I^m`.

The reverse implication is automatic for every ideal.  Hence the reflection
property is exactly the structural content needed for scaled Frobenius mark
compression.

The positive-dimensional coordinate, affine coordinate, linear-frame and
affine-frame centres constructed in the preceding files all satisfy this
property.  This packages a large family of coordinate calculations into one
interface.

The proposed scheme-level bridge is now precise: prove that every actual
regular centre used by the resolution algorithm has a Frobenius-normal power
filtration, for example by proving normality of its Rees algebra or reducedness
of its associated graded algebra.  That general theorem is not asserted here.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalCentre

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]

/-- Prime-power root reflection for every level of an ideal filtration. -/
def ReflectsFrobeniusPowers
    (p : Nat) (I : Ideal A) : Prop :=
  ∀ (e mark : Nat) (x : A),
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) → x ∈ I ^ mark

/-- The forward power implication is automatic for every ideal. -/
theorem power_mem_scaled_of_mem
    (I : Ideal A) (q mark : Nat) {x : A}
    (hx : x ∈ I ^ mark) :
    x ^ q ∈ I ^ (q * mark) := by
  have hp := Ideal.pow_mem_pow hx q
  simpa [pow_mul, Nat.mul_comm] using hp

/-- Reflection plus the automatic forward implication gives exact marked
heredity. -/
theorem power_mem_scaled_iff
    (p : Nat) (I : Ideal A)
    (hreflect : ReflectsFrobeniusPowers p I)
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔
      x ∈ I ^ mark := by
  constructor
  · exact hreflect e mark x
  · exact power_mem_scaled_of_mem I (p ^ e) mark

section Coordinate

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [Fintype α] [DecidableEq α]
variable [Fintype ι] [DecidableEq ι]
variable (p : Nat) [Fact p.Prime] [CharP K p]

/-- Positive-dimensional coordinate centres are Frobenius-normal. -/
theorem coordinateCentre_reflects :
    ReflectsFrobeniusPowers p
      (CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι)) := by
  intro e mark x hx
  exact
    (CoordinateCentreExactFrobeniusHeredity
      .frobeniusPower_mem_centreIdeal_pow_iff
        p e mark x).mp hx

/-- Affine coordinate centres are Frobenius-normal. -/
theorem affineCoordinateCentre_reflects (b : ι → K) :
    ReflectsFrobeniusPowers p
      (AffineCoordinateSubspaceHeredity.affineCentreIdeal
        (α := α) b) := by
  intro e mark x hx
  exact
    (AffineLinearFrameExactFrobeniusHeredity
      .frobeniusPower_mem_affineCentreIdeal_pow_iff
        p e mark b x).mp hx

/-- Linearly transported centres through the origin are Frobenius-normal. -/
theorem linearFrameCentre_reflects
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι)) :
    ReflectsFrobeniusPowers p
      (LinearFrameSubspaceHeredity.frameCentreIdeal F) := by
  intro e mark x hx
  exact
    (AffineLinearFrameExactFrobeniusHeredity
      .frobeniusPower_mem_frameCentreIdeal_pow_iff
        F p e mark x).mp hx

/-- Arbitrary globally framed affine linear centres are Frobenius-normal. -/
theorem affineFrameCentre_reflects
    (F : LinearCoordinateChange.FullFrame
      (K := K) (σ := α ⊕ ι))
    (b : ι → K) :
    ReflectsFrobeniusPowers p
      (AffineLinearFrameExactFrobeniusHeredity
        .affineFrameCentreIdeal F b) := by
  intro e mark x hx
  exact
    (AffineLinearFrameExactFrobeniusHeredity
      .frobeniusPower_mem_affineFrameCentreIdeal_pow_iff
        F p e mark b x).mp hx

end Coordinate

end

end FrobeniusNormalCentre
end Experimental
end PCRLean
