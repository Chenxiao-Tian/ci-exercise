import Mathlib
import PCRLean.Experimental.NormalConeLayer
import PCRLean.Experimental.CoordinateCentreExactFrobeniusHeredity
import PCRLean.Experimental.FrobeniusSupportDomain

/-!
# Frobenius-reduced normal cone of a coordinate centre

For the positive-dimensional coordinate centre, an element in `I^r` but not
`I^(r+1)` has at least one monomial of exact normal degree `r`. Prime-power
Frobenius sends that monomial to a supported monomial of exact normal degree
`p^e r`. Hence the power cannot enter `I^(p^e r + 1)`.

This proves `InitialPowerNonvanishing (p^e) I` in the quotient-layer language
of the normal cone. Consequently the normal cone is Frobenius-reduced in every
prime-power degree and the full filtration reflection theorem follows from the
graded-layer compiler.

The proof is deliberately independent of the already established direct
reflection theorem, showing that the associated-graded architecture has real
mathematical content rather than being a renamed conclusion.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateNormalConeFrobeniusReduced

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [DecidableEq α] [DecidableEq ι]
variable (p : Nat) [Fact p.Prime] [CharP K p]

abbrev I : Ideal (CoordinateBlowupChart.P
    (R := K) (α := α) (ι := ι)) :=
  CoordinateBlowupChart.centreIdeal
    (R := K) (α := α) (ι := ι)

/-- Every nonzero initial form for the coordinate centre has nonzero
`p^e`-th power in the scaled layer. -/
theorem initialPowerNonvanishing (e : Nat) :
    NormalConeLayer.InitialPowerNonvanishing (p ^ e)
      (I (K := K) (α := α) (ι := ι)) := by
  intro r x hx hini
  apply (NormalConeLayer.initialClass_ne_zero_iff
    (I (K := K) (α := α) (ι := ι)) (p ^ e * r)
    (x ^ (p ^ e))
    (NormalConeLayer.pow_mem_scaled
      (I (K := K) (α := α) (ι := ι)) (p ^ e) r hx)).mpr
  have hxNotNext :
      x ∉ (I (K := K) (α := α) (ι := ι)) ^ (r + 1) :=
    (NormalConeLayer.initialClass_ne_zero_iff
      (I (K := K) (α := α) (ι := ι)) r x hx).mp hini
  have horder :
      CoordinateCentreExactFrobeniusHeredity.NormalOrderGE
        (K := K) (α := α) (ι := ι) x r :=
    (CoordinateCentreExactFrobeniusHeredity.mem_centreIdeal_pow_iff_normalOrderGE
      x r).mp hx
  have hnotOrderNext :
      ¬ CoordinateCentreExactFrobeniusHeredity.NormalOrderGE
        (K := K) (α := α) (ι := ι) x (r + 1) := by
    intro hnext
    exact hxNotNext
      ((CoordinateCentreExactFrobeniusHeredity.mem_centreIdeal_pow_iff_normalOrderGE
        x (r + 1)).mpr hnext)
  let y := CoordinateCentreExactFrobeniusHeredity.normalPolynomialEquiv
    (K := K) (α := α) (ι := ι) x
  change FrobeniusSupportDomain.OrderGE y r at horder
  change ¬ FrobeniusSupportDomain.OrderGE y (r + 1) at hnotOrderNext
  unfold FrobeniusSupportDomain.OrderGE at horder hnotOrderNext
  push_neg at hnotOrderNext
  rcases hnotOrderNext with ⟨d, hd, hdeglt⟩
  have hdegeq :
      InitialFormFrobeniusCleaning.exponentDegree d = r := by
    apply Nat.le_antisymm
    · omega
    · exact horder d hd
  intro hxPowerNext
  have hpowerOrder :
      CoordinateCentreExactFrobeniusHeredity.NormalOrderGE
        (K := K) (α := α) (ι := ι)
        (x ^ (p ^ e)) (p ^ e * r + 1) :=
    (CoordinateCentreExactFrobeniusHeredity.mem_centreIdeal_pow_iff_normalOrderGE
      (x ^ (p ^ e)) (p ^ e * r + 1)).mp hxPowerNext
  unfold CoordinateCentreExactFrobeniusHeredity.NormalOrderGE at hpowerOrder
  rw [map_pow] at hpowerOrder
  change FrobeniusSupportDomain.OrderGE
    (y ^ (p ^ e)) (p ^ e * r + 1) at hpowerOrder
  have hscaled := FrobeniusSupportDomain.scaled_mem_support
    p e y hd
  have hbound := hpowerOrder
    (FrobeniusSupportDomain.scaleExponent (p ^ e) d) hscaled
  rw [FrobeniusSupportDomain.exponentDegree_scale, hdegeq] at hbound
  omega

/-- The coordinate normal cone has prime-power nonvanishing in every layer. -/
theorem frobeniusInitialPowerNonvanishing :
    ∀ e : Nat,
      NormalConeLayer.InitialPowerNonvanishing (p ^ e)
        (I (K := K) (α := α) (ι := ι)) :=
  initialPowerNonvanishing p

/-- Coordinate-centre Frobenius-normality derived through the normal-cone
quotient layers. -/
theorem reflectsFrobeniusPowers_via_normalCone :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (I (K := K) (α := α) (ι := ι)) :=
  NormalConeLayer.reflectsFrobeniusPowers_of_initialPowerNonvanishing
    p (I (K := K) (α := α) (ι := ι))
    (frobeniusInitialPowerNonvanishing p)

end

end CoordinateNormalConeFrobeniusReduced
end Experimental
end PCRLean
