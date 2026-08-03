import Mathlib
import PCRLean.FrobeniusPowerIdeal
import PCRLean.MarkedIdeal

/-!
# Mark scaling under Frobenius powers

A centre permissible for a lower-mark root packet remains permissible for its
Frobenius power after multiplying the mark by `p^e`.  If `I ⊆ C^b`, then

`F^e(I) ⊆ C^(b * p^e)`.

Together with power functoriality of controlled transforms, this is the
algebraic induction bridge that allows a centre word constructed for the root
packet at mark `b` to be reused for the Frobenius packet at mark `b*p^e`.
-/

namespace PCRLean
namespace FrobeniusMarkScaling

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (p e : Nat) [ExpChar A p]

/-- Frobenius image of a marked ideal is contained in the correspondingly
scaled centre power. -/
theorem powerIdeal_le_centre_pow_mul
    {I C : Ideal A} {b : Nat} (hI : I ≤ C ^ b) :
    FrobeniusPowerIdeal.powerIdeal (A := A) p e I ≤
      C ^ (b * (p ^ e)) := by
  rw [FrobeniusPowerIdeal.powerIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  change iterateFrobenius A p e x ∈ C ^ (b * p ^ e)
  rw [iterateFrobenius_def]
  have hxpow : x ^ (p ^ e) ∈ (C ^ b) ^ (p ^ e) :=
    Ideal.pow_mem_pow (hI hx) (p ^ e)
  simpa [pow_mul] using hxpow

/-- Marked-ideal formulation of Frobenius mark scaling. -/
theorem markedPacket_permissible
    {I C : Ideal A} {b : Nat}
    (hb : 0 < b * (p ^ e))
    (hI : I ≤ C ^ b) :
    MarkedIdeal.Permissible
      (R := A)
      ⟨FrobeniusPowerIdeal.powerIdeal (A := A) p e I,
        b * (p ^ e), hb⟩ C :=
  powerIdeal_le_centre_pow_mul (A := A) p e hI

/-- Exact power ideals preserve ideal powers under Frobenius. -/
theorem powerIdeal_pow
    (I : Ideal A) (b : Nat) :
    FrobeniusPowerIdeal.powerIdeal (A := A) p e (I ^ b) =
      (FrobeniusPowerIdeal.powerIdeal (A := A) p e I) ^ b := by
  simp [FrobeniusPowerIdeal.powerIdeal, Ideal.map_pow]

/-- One positive Frobenius level strictly lowers a positive scaled mark when
passing to the root packet. -/
theorem root_mark_strictly_smaller
    {b : Nat} (hb : 0 < b) (hp : 1 < p) (he : 0 < e) :
    b < b * (p ^ e) := by
  have hpPow : 1 < p ^ e := by
    exact one_lt_pow₀ hp he
  nlinarith

/-- More generally, the unscaled root mark is no larger, with equality only at
Frobenius exponent one. -/
theorem root_mark_le_scaled (b : Nat) :
    b ≤ b * (p ^ e) := by
  by_cases hb : b = 0
  · simp [hb]
  · have hpnonzero : 0 < p ^ e := by
      exact pow_pos (ExpChar.pos A p) e
    nlinarith

end

end FrobeniusMarkScaling
end PCRLean
