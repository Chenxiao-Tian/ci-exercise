import Mathlib
import PCRLean.CoordinateBlowupChart
import PCRLean.Experimental.CoordinateCentreExactFrobeniusHeredity

/-!
# Frobenius compatibility of coordinate controlled transforms

For a coordinate-centre blowup chart with pivot `k`, a marked equation
`f ∈ I^m` has chart image divisible by the exceptional factor `E_k^m`.
Instead of introducing a partial division operation, package a controlled
transform as a quotient together with the exact factorization

`chartMap_k(f) = E_k^m * quotient`.

Such data exist by ideal membership and are unique because the polynomial
exceptional factor is not a zero divisor.  If `f = g^(p^e)` and the marks are
scaled from `m` to `(p^e)m`, uniqueness then gives

`CT_k(g^(p^e),(p^e)m) = CT_k(g,m)^(p^e)`.

Thus Frobenius presentation compression commutes exactly with controlled
transform on every standard coordinate chart.  Overlap localization,
strict-transform saturation and packet reconstruction remain separate.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateControlledTransformHeredity

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)

/-- Exceptional pivot equation. -/
def exceptional (k : ι) : P (K := K) (α := α) (ι := ι) :=
  CoordinateBlowupChart.centreVar (R := K) (α := α) (ι := ι) k

/-- A controlled-transform quotient with its exact exceptional factorization. -/
structure Data
    (k : ι) (mark : Nat)
    (f : P (K := K) (α := α) (ι := ι)) where
  quotient : P (K := K) (α := α) (ι := ι)
  factorization :
    CoordinateBlowupChart.chartMap (R := K) (α := α) k f =
      (exceptional (K := K) (α := α) k) ^ mark * quotient

/-- Every marked-permissible equation has controlled-transform data in every
standard chart. -/
noncomputable def existsData
    (k : ι) (mark : Nat)
    (f : P (K := K) (α := α) (ι := ι))
    (hf : f ∈ (CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι)) ^ mark) :
    Data (K := K) (α := α) k mark f := by
  have hm := CoordinateBlowupChart.chartMap_mem_pivot_pow
    (R := K) (α := α) k hf
  rw [CoordinateBlowupChart.pivotIdeal,
    Ideal.span_singleton_pow] at hm
  rcases Ideal.mem_span_singleton'.mp hm with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa [exceptional, mul_comm] using hq.symm

/-- The exceptional factor is nonzero. -/
theorem exceptional_pow_ne_zero (k : ι) (mark : Nat) :
    (exceptional (K := K) (α := α) k) ^ mark ≠ 0 := by
  apply pow_ne_zero
  exact MvPolynomial.X_ne_zero (R := K) (Sum.inr k)

/-- Controlled-transform quotients are unique. -/
theorem quotient_unique
    {k : ι} {mark : Nat}
    {f : P (K := K) (α := α) (ι := ι)}
    (D₁ D₂ : Data (K := K) (α := α) k mark f) :
    D₁.quotient = D₂.quotient := by
  have hmul :
      (exceptional (K := K) (α := α) k) ^ mark * D₁.quotient =
        (exceptional (K := K) (α := α) k) ^ mark * D₂.quotient :=
    D₁.factorization.symm.trans D₂.factorization
  exact mul_left_cancel₀
    (exceptional_pow_ne_zero (K := K) (α := α) k mark) hmul

/-- Raising a controlled factorization to a power gives the scaled
factorization. -/
def powerData
    {k : ι} {mark : Nat}
    {g : P (K := K) (α := α) (ι := ι)}
    (D : Data (K := K) (α := α) k mark g)
    (q : Nat) :
    Data (K := K) (α := α) k (q * mark) (g ^ q) where
  quotient := D.quotient ^ q
  factorization := by
    calc
      CoordinateBlowupChart.chartMap (R := K) (α := α) k (g ^ q) =
          (CoordinateBlowupChart.chartMap (R := K) (α := α) k g) ^ q := by
            rw [map_pow]
      _ = (((exceptional (K := K) (α := α) k) ^ mark) *
          D.quotient) ^ q := by rw [D.factorization]
      _ = ((exceptional (K := K) (α := α) k) ^ mark) ^ q *
          D.quotient ^ q := by rw [mul_pow]
      _ = (exceptional (K := K) (α := α) k) ^ (q * mark) *
          D.quotient ^ q := by
            rw [← pow_mul]
            congr 2
            exact Nat.mul_comm mark q

/-- Any controlled transform of a power is the corresponding power of the
root controlled transform. -/
theorem quotient_power_eq
    {k : ι} {mark : Nat}
    {g : P (K := K) (α := α) (ι := ι)}
    (q : Nat)
    (Droot : Data (K := K) (α := α) k mark g)
    (Dpower : Data (K := K) (α := α) k (q * mark) (g ^ q)) :
    Dpower.quotient = Droot.quotient ^ q := by
  exact quotient_unique Dpower (powerData Droot q)

/-- Prime-power form of controlled-transform heredity. -/
theorem quotient_primePower_eq
    (p : Nat) [Fact p.Prime] [CharP K p]
    {k : ι} {mark : Nat}
    {g : P (K := K) (α := α) (ι := ι)}
    (e : Nat)
    (Droot : Data (K := K) (α := α) k mark g)
    (Dpower : Data (K := K) (α := α) k
      ((p ^ e) * mark) (g ^ (p ^ e))) :
    Dpower.quotient = Droot.quotient ^ (p ^ e) :=
  quotient_power_eq (p ^ e) Droot Dpower

/-- A root marked-power certificate produces compatible controlled transforms
for the root and its prime power. -/
noncomputable def canonicalCompatibleData
    (p : Nat) [Fact p.Prime] [CharP K p]
    (k : ι) (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι))
    (hg : g ∈ (CoordinateBlowupChart.centreIdeal
      (R := K) (α := α) (ι := ι)) ^ mark) :
    Data (K := K) (α := α) k ((p ^ e) * mark) (g ^ (p ^ e)) :=
  powerData (existsData k mark g hg) (p ^ e)

end

end CoordinateControlledTransformHeredity
end Experimental
end PCRLean
