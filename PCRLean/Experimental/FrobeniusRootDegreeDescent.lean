import Mathlib
import PCRLean.GenerationalRank
import PCRLean.Experimental.PerfectFrobeniusRankZeroEscape

/-!
# Experimental degree descent for certified Frobenius roots

Let `p` be prime.  Replacing a nonconstant polynomial `F = G^p` by its root `G`
strictly lowers total degree.  Therefore an execution consisting entirely of
certified nonconstant Frobenius-root steps cannot be infinite.

For a nonzero pure `p^e`-form over a perfect field, the coefficientwise linear
root has positive total degree and its `p^e`-th power is the original form, so
the higher diagnostic collapses directly to a linear packet.

The theorem is a genuine U5 termination backend, conditional only on existence
of the certified polynomial roots.  It does not prove that every derivative-
zero or Hasse-rank-zero polynomial over an arbitrary residue field is a
`p`-th power.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusRootDegreeDescent

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v}
variable (p : Nat) [Fact p.Prime]

/-- One certified Frobenius-root transition.  The first argument is the parent
polynomial and the second is its chosen root. -/
def RootStep (parent child : MvPolynomial σ K) : Prop :=
  parent = child ^ p ∧ 0 < child.totalDegree

/-- Prime Frobenius root extraction strictly lowers total degree. -/
theorem totalDegree_decreases
    {parent child : MvPolynomial σ K}
    (h : RootStep p parent child) :
    child.totalDegree < parent.totalDegree := by
  rcases h with ⟨rfl, hchild⟩
  rw [MvPolynomial.totalDegree_pow]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/-- No infinite chain of certified nonconstant Frobenius-root extractions. -/
theorem no_infinite_root_chain :
    ¬ ∃ f : Nat → MvPolynomial σ K,
      ∀ n, RootStep p (f n) (f (n + 1)) := by
  rintro ⟨f, hf⟩
  exact PCRLean.noInfiniteDescending Nat.lt_wfRel.wf
    (fun n => (f n).totalDegree)
    (fun n => totalDegree_decreases p (hf n))

/-- A `p^e`-th root with positive degree gives a strict one-shot degree drop. -/
theorem iteratedRoot_totalDegree_lt
    (e : Nat) (he : 0 < e)
    (g : MvPolynomial σ K) (hg : 0 < g.totalDegree) :
    g.totalDegree < (g ^ (p ^ e)).totalDegree := by
  rw [MvPolynomial.totalDegree_pow]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpow : 2 ≤ p ^ e := by
    exact two_le_pow₀ hp he
  omega

section Perfect

variable [CharP K p] [PerfectField K p]
variable [Fintype σ] [DecidableEq σ]

/-- A nonzero pure higher-Frobenius form has a nonconstant recovered linear
root. -/
theorem rootLinearPolynomial_totalDegree_pos
    (coeff : σ → K) (e : Nat)
    (hpure :
      PerfectFrobeniusRankZeroEscape.pureFrobeniusPolynomial
        p coeff e ≠ 0) :
    0 < (PerfectFrobeniusRankZeroEscape.rootLinearPolynomial
      p coeff e).totalDegree := by
  have hroot :=
    PerfectFrobeniusRankZeroEscape.rootFunctional_ne_zero_of_pure_ne_zero
      p coeff e hpure
  have hpoly :
      PerfectFrobeniusRankZeroEscape.rootLinearPolynomial p coeff e ≠ 0 := by
    intro hz
    apply hroot
    apply FunctionalPacketIdeal.integrationMap.injective
    rw [PerfectFrobeniusRankZeroEscape.functionalPolynomial_rootFunctional]
    exact hz
  have hnotconst :
      ¬ PerfectFrobeniusRankZeroEscape.rootLinearPolynomial p coeff e ∈
        MvPolynomial.C '' (Set.univ : Set K) := by
    intro hconst
    rcases hconst with ⟨a, ha, hEq⟩
    have hcoeff : ∀ i, PerfectFrobeniusRankZeroEscape.rootRow p coeff e i = 0 := by
      intro i
      have hX := congrArg
        (MvPolynomial.coeff (Finsupp.single i 1)) hEq
      simpa [PerfectFrobeniusRankZeroEscape.rootLinearPolynomial,
        LinearPacketIdeal.linearPolynomial] using hX
    apply hpoly
    rw [PerfectFrobeniusRankZeroEscape.rootLinearPolynomial,
      LinearPacketIdeal.linearPolynomial]
    simp [hcoeff]
  exact MvPolynomial.totalDegree_pos.mpr hnotconst

/-- A nonzero pure `p^e`-form with `e > 0` strictly decreases total degree when
replaced by its recovered linear root. -/
theorem pureFrobenius_root_degree_lt
    (coeff : σ → K) (e : Nat) (he : 0 < e)
    (hpure :
      PerfectFrobeniusRankZeroEscape.pureFrobeniusPolynomial
        p coeff e ≠ 0) :
    (PerfectFrobeniusRankZeroEscape.rootLinearPolynomial p coeff e).totalDegree <
      (PerfectFrobeniusRankZeroEscape.pureFrobeniusPolynomial
        p coeff e).totalDegree := by
  rw [← PerfectFrobeniusRankZeroEscape.rootLinearPolynomial_pow p coeff e]
  exact iteratedRoot_totalDegree_lt p e he _
    (rootLinearPolynomial_totalDegree_pos p coeff e hpure)

end Perfect

end

end FrobeniusRootDegreeDescent
end Experimental
end PCRLean
