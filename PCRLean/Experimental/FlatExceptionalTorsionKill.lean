import Mathlib
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness kills exceptional power torsion

Let `u` be the equation of an effective Cartier divisor on a base ring `R`.
If an `R`-module is flat, multiplication by `u` is injective.  Hence no
nonzero element can be killed by any positive power of `u`.  In the X038
application, once the purified associated-graded owner module is flat over the
regular carrier, its purification--grading defect

```text
H^0_(u)(gr_L(N / H^0_(u)(N)))
```

must vanish.

The file proves only this module-theoretic endpoint.  It does not construct a
flatifier, identify a geometric exceptional equation, or compare ambient and
carrier transforms.
-/

namespace PCRLean
namespace Experimental
namespace FlatExceptionalTorsionKill

noncomputable section

open scoped nonZeroDivisors

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- On a flat module, a power of a base nonzerodivisor kills only zero. -/
theorem eq_zero_of_pow_smul_eq_zero
    [Module.Flat R M]
    {q : R} (hq : q ∈ R⁰)
    {n : ℕ} {x : M}
    (hx : q ^ n • x = 0) :
    x = 0 := by
  have hreg : IsSMulRegular M q :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hq
  induction n with
  | zero =>
      simpa using hx
  | succ n ih =>
      apply ih
      apply hreg
      simpa [pow_succ, smul_smul, mul_comm] using hx

/-- Any submodule all of whose elements are killed by some power of the
exceptional equation is zero after flatness. -/
theorem submodule_eq_bot_of_power_torsion
    [Module.Flat R M]
    {q : R} (hq : q ∈ R⁰)
    (E : Submodule R M)
    (hE : ∀ x, x ∈ E → ∃ n : ℕ, q ^ n • x = 0) :
    E = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := hE x hx
  exact eq_zero_of_pow_smul_eq_zero hq hn

/-- The same endpoint simultaneously for a finite owner/divisor packet. -/
theorem finite_packet_vanishes
    {ι : Type w} [Fintype ι]
    (Piece : ι → Type v)
    [∀ i, AddCommGroup (Piece i)]
    [∀ i, Module R (Piece i)]
    [∀ i, Module.Flat R (Piece i)]
    {q : R} (hq : q ∈ R⁰)
    (E : ∀ i, Submodule R (Piece i))
    (hE : ∀ i x, x ∈ E i → ∃ n : ℕ, q ^ n • x = 0) :
    ∀ i, E i = ⊥ := by
  intro i
  exact submodule_eq_bot_of_power_torsion hq (E i) (hE i)

end

end FlatExceptionalTorsionKill
end Experimental
end PCRLean
