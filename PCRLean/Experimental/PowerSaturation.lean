import Mathlib
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Power saturation and quotient torsion

On one affine blowup chart, strict transform is pullback modulo power torsion
in the exceptional chart parameter `q`.  If `N ≤ M`, then a class in `M ⧸ N`
is `q`-power torsion exactly when its representative lies in the relative
`q`-power saturation of `N` in `M`.

This elementary fact is the algebraic leaf behind the X038
Tor--Valabrega common-core proposal.  It identifies the saturation defect with
the exceptional-power torsion of a quotient.  It does not construct a blowup,
a Rees module, a coherent defect sheaf, or a resolution algorithm.
-/

namespace PCRLean
namespace Experimental
namespace PowerSaturation

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Relative saturation of `N` by powers of the scalar `q`. -/
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
    rintro r x ⟨n, hx⟩
    refine ⟨n, ?_⟩
    rw [smul_comm (q ^ n) r x]
    exact N.smul_mem r hx

@[simp] theorem mem_powerSaturation_iff
    (q : R) (N : Submodule R M) (x : M) :
    x ∈ powerSaturation q N ↔ ∃ n : ℕ, q ^ n • x ∈ N :=
  Iff.rfl

/-- Every submodule is contained in its power saturation. -/
theorem le_powerSaturation (q : R) (N : Submodule R M) :
    N ≤ powerSaturation q N := by
  intro x hx
  exact ⟨0, by simpa using hx⟩

/-- Power saturation is monotone in the submodule. -/
theorem powerSaturation_mono
    (q : R) {N P : Submodule R M} (hNP : N ≤ P) :
    powerSaturation q N ≤ powerSaturation q P := by
  rintro x ⟨n, hx⟩
  exact ⟨n, hNP hx⟩

/-- Saturating twice by the same scalar adds no new elements. -/
theorem powerSaturation_idem (q : R) (N : Submodule R M) :
    powerSaturation q (powerSaturation q N) = powerSaturation q N := by
  apply le_antisymm
  · rintro x ⟨n, m, hxm⟩
    refine ⟨m + n, ?_⟩
    simpa [pow_add, smul_smul] using hxm
  · exact le_powerSaturation q (powerSaturation q N)

/-- The submodule of elements killed by some power of `q`. -/
def powerTorsion (q : R) : Submodule R M :=
  powerSaturation q ⊥

@[simp] theorem mem_powerTorsion_iff
    (q : R) (x : M) :
    x ∈ powerTorsion (M := M) q ↔ ∃ n : ℕ, q ^ n • x = 0 := by
  simp [powerTorsion, powerSaturation]

/-- A quotient class is killed by a power of `q` exactly when its representative
lies in the relative power saturation. -/
theorem quotient_mk_mem_powerTorsion_iff
    (q : R) (N : Submodule R M) (x : M) :
    N.mkQ x ∈ powerTorsion (M := M ⧸ N) q ↔
      x ∈ powerSaturation q N := by
  rw [mem_powerTorsion_iff, mem_powerSaturation_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmk : N.mkQ (q ^ n • x) = 0 := by
      simpa using hn
    exact (Submodule.Quotient.mk_eq_zero N).mp hmk
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmk : N.mkQ (q ^ n • x) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr hn
    simpa using hmk

/-- Saturation is trivial exactly when every power-torsion quotient class is
already zero.  This is the abstract Valabrega-style exactness gate. -/
theorem powerSaturation_eq_iff_quotient_powerTorsion_zero
    (q : R) (N : Submodule R M) :
    powerSaturation q N = N ↔
      ∀ x : M,
        N.mkQ x ∈ powerTorsion (M := M ⧸ N) q → N.mkQ x = 0 := by
  constructor
  · intro h x hx
    have hsat : x ∈ powerSaturation q N :=
      (quotient_mk_mem_powerTorsion_iff q N x).mp hx
    exact (Submodule.Quotient.mk_eq_zero N).mpr (h ▸ hsat)
  · intro h
    apply le_antisymm
    · intro x hx
      have htor : N.mkQ x ∈ powerTorsion (M := M ⧸ N) q :=
        (quotient_mk_mem_powerTorsion_iff q N x).mpr hx
      exact (Submodule.Quotient.mk_eq_zero N).mp (h x htor)
    · exact le_powerSaturation q N

/-- If multiplication by `q` is regular on the quotient, no higher power of
`q` can create new saturation.  This is the algebraic flat-kill endpoint for
one exceptional parameter. -/
theorem powerSaturation_eq_of_isSMulRegular_quotient
    (q : R) (N : Submodule R M)
    (hreg : IsSMulRegular (M ⧸ N) q) :
    powerSaturation q N = N := by
  have hpow : ∀ n : ℕ, ∀ x : M, q ^ n • x ∈ N → x ∈ N := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        apply mem_of_isSMulRegular_quotient_of_smul_mem hreg
        apply ih (q • x)
        simpa [pow_succ, smul_smul] using hx
  apply le_antisymm
  · rintro x ⟨n, hx⟩
    exact hpow n x hx
  · exact le_powerSaturation q N

/-- A regular exceptional parameter has no power torsion. -/
theorem powerTorsion_eq_bot_of_isSMulRegular
    (q : R) (hreg : IsSMulRegular M q) :
    powerTorsion (M := M) q = ⊥ := by
  apply Submodule.eq_bot_iff.mpr
  intro x hx
  rcases (mem_powerTorsion_iff q x).mp hx with ⟨n, hn⟩
  induction n with
  | zero =>
      simpa using hn
  | succ n ih =>
      apply ih
      apply hreg
      simpa [pow_succ, smul_smul, mul_comm] using hn

end

end PowerSaturation
end Experimental
end PCRLean
