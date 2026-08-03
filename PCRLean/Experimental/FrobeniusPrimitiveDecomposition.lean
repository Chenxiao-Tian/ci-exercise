import Mathlib
import PCRLean.Experimental.PDerivFrobeniusDescent

/-!
# Finite Frobenius-primitive decomposition

Over a perfect field of characteristic `p`, a nonconstant polynomial with all
first partial derivatives zero has an explicit `p`-th root of strictly smaller
total degree.  Strong induction therefore factors every polynomial as

`f = primitive ^ (p^e)`

where the final factor is either constant or has a nonzero first partial
derivative.  This is a finite, choice-free rank-zero exit at the polynomial
level.  It does not yet identify the geometric Hasse core with the principal
ideal of the chosen polynomial, nor prove descent over imperfect fields.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusPrimitiveDecomposition

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

open PDerivFrobeniusDescent

/-- A terminal polynomial for first-order Frobenius descent: it is constant or
some first partial derivative is visible. -/
def FrobeniusPrimitive (f : MvPolynomial σ K) : Prop :=
  f.totalDegree = 0 ∨ DerivativeVisible f

/-- Every polynomial has a finite Frobenius-depth decomposition ending at a
constant or derivative-visible factor. -/
theorem exists_frobeniusPrimitive_decomposition
    (f : MvPolynomial σ K) :
    ∃ e : Nat, ∃ g : MvPolynomial σ K,
      f = g ^ (p ^ e) ∧ FrobeniusPrimitive g := by
  let P : Nat → Prop := fun n =>
    ∀ f : MvPolynomial σ K, f.totalDegree = n →
      ∃ e : Nat, ∃ g : MvPolynomial σ K,
        f = g ^ (p ^ e) ∧ FrobeniusPrimitive g
  have hstep : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih f hdegree
    by_cases hn : n = 0
    · refine ⟨0, f, ?_, Or.inl ?_⟩
      · simp
      · simpa [hdegree] using hn
    · have hfpos : 0 < f.totalDegree := by
        omega
      rcases visible_or_strict_root p f hfpos with hvis | hroot
      · exact ⟨0, f, by simp, Or.inr hvis⟩
      · rcases hroot with ⟨g, hfg, hgpos, hglt⟩
        have hglt_n : g.totalDegree < n := by
          simpa [hdegree] using hglt
        rcases ih g.totalDegree hglt_n g rfl with
          ⟨e, h, hgh, hprimitive⟩
        refine ⟨e + 1, h, ?_, hprimitive⟩
        calc
          f = g ^ p := hfg
          _ = (h ^ (p ^ e)) ^ p := by rw [hgh]
          _ = h ^ ((p ^ e) * p) := by rw [← pow_mul]
          _ = h ^ (p ^ (e + 1)) := by rw [pow_succ]
  exact (Nat.strong_induction_on f.totalDegree hstep) f rfl

/-- A nonconstant derivative-invisible polynomial has positive Frobenius depth
in some primitive decomposition. -/
theorem exists_positive_depth_of_all_pderiv_zero
    (f : MvPolynomial σ K)
    (hf : 0 < f.totalDegree)
    (hderiv : ∀ i, MvPolynomial.pderiv i f = 0) :
    ∃ e : Nat, 0 < e ∧ ∃ g : MvPolynomial σ K,
      f = g ^ (p ^ e) ∧ FrobeniusPrimitive g := by
  let r := PDerivFrobeniusDescent.derivativeRoot p f
  have hfr : f = r ^ p :=
    (PDerivFrobeniusDescent.derivativeRoot_pow p f hderiv).symm
  obtain ⟨e, g, hrg, hgprim⟩ :=
    exists_frobeniusPrimitive_decomposition p r
  refine ⟨e + 1, by omega, g, ?_, hgprim⟩
  calc
    f = r ^ p := hfr
    _ = (g ^ (p ^ e)) ^ p := by rw [hrg]
    _ = g ^ ((p ^ e) * p) := by rw [← pow_mul]
    _ = g ^ (p ^ (e + 1)) := by rw [pow_succ]

end

end FrobeniusPrimitiveDecomposition
end Experimental
end PCRLean
