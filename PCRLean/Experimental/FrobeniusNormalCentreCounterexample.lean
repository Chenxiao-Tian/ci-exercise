import Mathlib.Algebra.DualNumber
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Nonreduced no-go for Frobenius-normal centres

The Frobenius-normal reflection property is not formal and does not hold in an
arbitrary ambient ring.  In the dual-number ring `K[ε]`, the nilpotent element
`ε` satisfies `ε^2 = 0` but `ε ≠ 0`.  For the zero ideal this gives

`ε^2 ∈ (0)^2` while `ε ∉ (0)`.

Thus the zero ideal fails two-power reflection in every nontrivial dual-number
ring.  Any general proof for regular centres must use reducedness or a stronger
normality property of the associated graded/Rees filtration; regularity of the
closed centre alone is insufficient in a nonreduced ambient ring.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalCentreCounterexample

noncomputable section

universe u

variable {K : Type u} [CommRing K] [Nontrivial K]

/-- The dual-number infinitesimal is nonzero over a nontrivial base ring. -/
theorem eps_ne_zero :
    (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro h
  have hsnd := congrArg (TrivSqZeroExt.snd : DualNumber K → K) h
  simpa using hsnd

/-- The square-zero infinitesimal lies in the square of the zero ideal. -/
theorem eps_sq_mem_bottom_sq :
    (DualNumber.eps : DualNumber K) ^ 2 ∈
      (⊥ : Ideal (DualNumber K)) ^ 2 := by
  simp [DualNumber.eps_pow_two]

/-- But the infinitesimal itself is not in the zero ideal. -/
theorem eps_not_mem_bottom :
    (DualNumber.eps : DualNumber K) ∉
      (⊥ : Ideal (DualNumber K)) := by
  simpa using eps_ne_zero (K := K)

/-- The zero ideal of a nontrivial dual-number ring is not Frobenius-normal for
`p = 2`. -/
theorem bottom_not_reflects_twoPowers :
    ¬ FrobeniusNormalCentre.ReflectsFrobeniusPowers 2
      (⊥ : Ideal (DualNumber K)) := by
  intro hreflect
  have hmem :
      (DualNumber.eps : DualNumber K) ^ (2 ^ 1) ∈
        (⊥ : Ideal (DualNumber K)) ^ ((2 ^ 1) * 1) := by
    simpa using eps_sq_mem_bottom_sq (K := K)
  have hroot := hreflect 1 1 (DualNumber.eps : DualNumber K) hmem
  simpa using (eps_not_mem_bottom (K := K) hroot)

end

end FrobeniusNormalCentreCounterexample
end Experimental
end PCRLean
