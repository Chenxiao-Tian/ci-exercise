import Mathlib
import PCRLean.Experimental.PDerivFrobeniusDescent

/-!
# Frobenius cleaning of a rank-zero initial form

Geometric rank zero is normally a statement about the lowest-order homogeneous
initial form, not about the whole local equation. This file isolates the
correct affine graded bridge.

Write `f = F + h`, where `F` is homogeneous of degree `n` and every monomial of
`h` has degree strictly larger than `n`. If every first partial derivative of
`F` vanishes, then over a perfect field `F = G^p`. Subtracting the actual
polynomial `G^p` from `f` leaves exactly `h`, hence strictly raises the order.
The argument uses only the finite support of the given polynomial and therefore
works for an arbitrary variable type.

A general resolution theorem must still construct this initial decomposition in
regular local charts and prove compatibility with owners, boundaries and
transforms.
-/

namespace PCRLean
namespace Experimental
namespace InitialFormFrobeniusCleaning

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

/-- Total degree of one exponent vector. -/
def exponentDegree (m : σ →₀ Nat) : Nat :=
  m.sum fun _ e => e

/-- Every supported monomial has the same degree. -/
def HomogeneousDegree (n : Nat) (F : MvPolynomial σ K) : Prop :=
  ∀ m ∈ F.support, exponentDegree m = n

/-- Every supported monomial has degree strictly above `n`. -/
def HigherThan (n : Nat) (h : MvPolynomial σ K) : Prop :=
  ∀ m ∈ h.support, n < exponentDegree m

/-- A lowest-order homogeneous decomposition. -/
structure InitialDecomposition
    (f : MvPolynomial σ K) (n : Nat) where
  initial : MvPolynomial σ K
  remainder : MvPolynomial σ K
  equation : f = initial + remainder
  initial_homogeneous : HomogeneousDegree n initial
  remainder_higher : HigherThan n remainder

namespace InitialDecomposition

variable {f : MvPolynomial σ K} {n : Nat}
variable (D : InitialDecomposition f n)

/-- Rank-zero initial form condition. -/
def RankZero : Prop :=
  ∀ i, MvPolynomial.pderiv i D.initial = 0

/-- Canonical perfect-field root of the initial form. -/
def root : MvPolynomial σ K :=
  PDerivFrobeniusDescent.derivativeRoot p D.initial

/-- The initial form is exactly the `p`-th power of the canonical root. -/
theorem root_pow (hrank : D.RankZero) :
    (D.root p) ^ p = D.initial := by
  exact PDerivFrobeniusDescent.derivativeRoot_pow p D.initial hrank

/-- Cleaning by the lifted Frobenius root removes the entire initial form. -/
theorem cleaned_eq_remainder (hrank : D.RankZero) :
    f - (D.root p) ^ p = D.remainder := by
  rw [D.equation, D.root_pow p hrank]
  ring

/-- The cleaned equation has no supported monomial of degree at most `n`. -/
theorem cleaned_higher (hrank : D.RankZero) :
    HigherThan n (f - (D.root p) ^ p) := by
  rw [D.cleaned_eq_remainder p hrank]
  exact D.remainder_higher

/-- A nonzero rank-zero initial form has degree divisible by the characteristic. -/
theorem prime_dvd_initial_degree
    (hrank : D.RankZero) (hinit : D.initial ≠ 0) : p ∣ n := by
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hinit
  have hcoord : ∀ i, p ∣ m i := by
    intro i
    exact PDerivFrobeniusDescent.exponent_dvd_of_pderiv_eq_zero
      p D.initial i (hrank i) hm
  have hsum : p ∣ exponentDegree m := by
    unfold exponentDegree
    exact Finset.dvd_sum fun i hi => hcoord i
  rw [D.initial_homogeneous m hm] at hsum
  exact hsum

/-- If the initial form has positive degree, its canonical root has strictly
smaller total degree. -/
theorem root_totalDegree_lt
    (hrank : D.RankZero)
    (hpositive : 0 < D.initial.totalDegree) :
    (D.root p).totalDegree < D.initial.totalDegree :=
  PDerivFrobeniusDescent.derivativeRoot_totalDegree_lt
    p D.initial hrank hpositive

end InitialDecomposition

end

end InitialFormFrobeniusCleaning
end Experimental
end PCRLean
