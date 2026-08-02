import Mathlib
import PCRLean.Algebra.FrobeniusPolynomialRoot
import PCRLean.Framework.RankedSystem

/-!
# Finite univariate Frobenius-root extraction

For a polynomial over a perfect field of characteristic `p`, derivative zero
produces a canonical `p`-th root.  Repeating this operation cannot continue
indefinitely: positive polynomial degree is divided by the prime `p` at every
root step.  The terminal packet is either constant or has nonzero derivative.

This is a genuine arbitrary-input theorem for one polynomial direction.  It is
not an arbitrary-dimensional resolution theorem and does not root coefficient
functions on a positive-dimensional base.
-/

noncomputable section

namespace PCRLean.Algebra.FrobeniusExtractionProgram

open Polynomial

variable {K : Type*} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The degree is the well-founded extraction rank. -/
def rank (f : K[X]) : ℕ := f.natDegree

/-- A packet is terminal when it is constant or has a visible differential. -/
def terminal (f : K[X]) : Prop :=
  f.natDegree = 0 ∨ derivative f ≠ 0

/-- Terminality is the exact certified outcome for this extractor. -/
def resolved (f : K[X]) : Prop := terminal p f

/-- One canonical Frobenius-root extraction step. -/
inductive Step : K[X] → K[X] → Prop
  | extract (f : K[X])
      (hder : derivative f = 0)
      (hdeg : 0 < f.natDegree) :
      Step (PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial p f) f

/-- The original degree is the characteristic prime times the root degree. -/
theorem degree_eq_prime_mul_root_degree {f : K[X]}
    (hder : derivative f = 0) :
    f.natDegree =
      p * (PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial p f).natDegree := by
  rw [← PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial_pow_of_derivative_eq_zero
    p hder]
  exact Polynomial.natDegree_pow _ _

/-- Every nontrivial root extraction strictly lowers polynomial degree. -/
theorem root_degree_strict_drop {f : K[X]}
    (hder : derivative f = 0) (hdeg : 0 < f.natDegree) :
    (PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial p f).natDegree <
      f.natDegree := by
  let d := (PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial p f).natDegree
  have hEq : f.natDegree = p * d := by
    simpa [d] using degree_eq_prime_mul_root_degree p hder
  have hmulpos : 0 < p * d := by simpa [hEq] using hdeg
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    simp [hd0] at hmulpos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfirst : d < 2 * d := by omega
  have hsecond : 2 * d ≤ p * d := Nat.mul_le_mul_right d hp2
  rw [hEq]
  exact hfirst.trans_le hsecond

/-- Every extraction edge strictly lowers the rank. -/
theorem step_decreases {child parent : K[X]}
    (h : Step (K := K) p child parent) :
    rank p child < rank p parent := by
  cases h with
  | extract f hder hdeg =>
      exact root_degree_strict_drop p hder hdeg

/-- Every nonterminal packet admits its canonical root step. -/
theorem progress (f : K[X]) :
    ¬ terminal p f → ∃ g, Step (K := K) p g f := by
  intro hterm
  have hdeg : 0 < f.natDegree := by
    by_contra h
    exact hterm (Or.inl (Nat.eq_zero_of_not_pos h))
  have hder : derivative f = 0 := by
    by_contra h
    exact hterm (Or.inr h)
  exact ⟨PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial p f,
    Step.extract f hder hdeg⟩

/-- The complete finite root-extraction program. -/
def program : PCRLean.Framework.CertifiedProgram where
  State := K[X]
  step := Step (K := K) p
  rank := rank p
  step_decreases := step_decreases p
  terminal := terminal p
  resolved := resolved p
  terminal_resolved := by intro _ h; exact h
  progress := progress p

/-- Every univariate polynomial reaches a constant packet or one with nonzero
formal derivative after finitely many canonical Frobenius-root extractions. -/
theorem reaches_visible_or_constant (f : K[X]) :
    ∃ g, Relation.ReflTransGen (Step (K := K) p) g f ∧
      (g.natDegree = 0 ∨ derivative g ≠ 0) :=
  (program (K := K) p).reaches_resolved f

end PCRLean.Algebra.FrobeniusExtractionProgram
