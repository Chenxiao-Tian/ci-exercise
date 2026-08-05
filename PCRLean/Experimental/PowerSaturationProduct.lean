import Mathlib

/-!
# Product law for power saturation

For a scalar `q` and a submodule `N ≤ M`, the relative power saturation is

`Sat_q(N) = {x | q^n • x ∈ N for some n}`.

If `q` and `r` commute, saturation by their product is exactly successive
saturation by the two scalars.  Over a commutative ring this gives

`Sat_(q*r)(N) = Sat_r(Sat_q(N))`.

This is the module-theoretic shadow of the Cartier-divisor identity
`η_q η_r = η_(q*r)`.  It is the atomic algebra behind the X041 proposal that a
centre word can be compressed, after retaining its total exceptional divisor,
to a factorization-independent saturated transform.

No scheme-level blowup, derived décalage, strict transform, base-change, or
resolution theorem is asserted here.
-/

namespace PCRLean
namespace Experimental
namespace PowerSaturationProduct

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Relative saturation of `N` by powers of `q`. -/
def powerSaturation (q : R) (N : Submodule R M) : Submodule R M where
  carrier := {x | ∃ n : ℕ, q ^ n • x ∈ N}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    have hx' : q ^ (n + m) • x ∈ N := by
      simpa [pow_add, smul_smul, mul_comm] using N.smul_mem (q ^ m) hx
    have hy' : q ^ (n + m) • y ∈ N := by
      simpa [pow_add, smul_smul] using N.smul_mem (q ^ n) hy
    simpa [smul_add] using N.add_mem hx' hy'
  smul_mem' := by
    rintro a x ⟨n, hx⟩
    refine ⟨n, ?_⟩
    rw [smul_comm (q ^ n) a x]
    exact N.smul_mem a hx

@[simp] theorem mem_powerSaturation_iff
    (q : R) (N : Submodule R M) (x : M) :
    x ∈ powerSaturation q N ↔ ∃ n : ℕ, q ^ n • x ∈ N :=
  Iff.rfl

/-- Saturation by the unit scalar changes nothing. -/
@[simp] theorem powerSaturation_one (N : Submodule R M) :
    powerSaturation (1 : R) N = N := by
  apply le_antisymm
  · rintro x ⟨n, hx⟩
    simpa using hx
  · intro x hx
    exact ⟨0, by simpa using hx⟩

/-- Every submodule is contained in its power saturation. -/
theorem le_powerSaturation (q : R) (N : Submodule R M) :
    N ≤ powerSaturation q N := by
  intro x hx
  exact ⟨0, by simpa using hx⟩

/-- Saturation is monotone in the submodule. -/
theorem powerSaturation_mono
    (q : R) {N P : Submodule R M} (hNP : N ≤ P) :
    powerSaturation q N ≤ powerSaturation q P := by
  rintro x ⟨n, hx⟩
  exact ⟨n, hNP hx⟩

/-- Saturating twice by the same scalar is idempotent. -/
theorem powerSaturation_idem (q : R) (N : Submodule R M) :
    powerSaturation q (powerSaturation q N) = powerSaturation q N := by
  apply le_antisymm
  · rintro x ⟨n, m, hxm⟩
    refine ⟨m + n, ?_⟩
    simpa [pow_add, smul_smul] using hxm
  · exact le_powerSaturation q (powerSaturation q N)

/-- Saturation by a product is successive saturation. -/
theorem powerSaturation_mul
    (q r : R) (N : Submodule R M) :
    powerSaturation (q * r) N =
      powerSaturation r (powerSaturation q N) := by
  apply le_antisymm
  · rintro x ⟨n, hx⟩
    refine ⟨n, n, ?_⟩
    simpa [mul_pow, smul_smul] using hx
  · rintro x ⟨m, n, hx⟩
    refine ⟨n + m, ?_⟩
    have hscaled := N.smul_mem (q ^ m * r ^ n) hx
    simpa [mul_pow, pow_add, smul_smul, mul_assoc, mul_comm, mul_left_comm]
      using hscaled

/-- The order of two saturation steps is irrelevant. -/
theorem powerSaturation_commute
    (q r : R) (N : Submodule R M) :
    powerSaturation r (powerSaturation q N) =
      powerSaturation q (powerSaturation r N) := by
  rw [← powerSaturation_mul, mul_comm, powerSaturation_mul]

/-- Saturation by a scalar power is repeated saturation in one step. -/
theorem powerSaturation_pow_two
    (q : R) (N : Submodule R M) :
    powerSaturation (q ^ 2) N =
      powerSaturation q (powerSaturation q N) := by
  simpa [pow_two] using powerSaturation_mul q q N

end

end PowerSaturationProduct
end Experimental
end PCRLean
