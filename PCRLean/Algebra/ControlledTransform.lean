import Mathlib

/-!
# Exact controlled-transform certificates

A controlled transform is not an informal division by an exceptional factor.
It is an equality in a specified chart ring.  This file records that equality
and proves its basic composition law.  Geometry must additionally certify that
the chart map, centre, boundary, and overlap data are the intended ones.
-/

namespace PCRLean.Algebra.ControlledTransform

variable {R : Type*} [CommRing R]

/-- An exact factorization of the total transform by the marked exceptional
power. -/
structure Certificate (total exceptional controlled : R) (mark : ℕ) : Prop where
  factorization : total = exceptional ^ mark * controlled

namespace Certificate

/-- The controlled transform is unchanged after rewriting the total transform
by the certified equality. -/
theorem eq_exceptional_pow_mul {total exceptional controlled : R} {mark : ℕ}
    (h : Certificate total exceptional controlled mark) :
    total = exceptional ^ mark * controlled :=
  h.factorization

/-- Two controlled-transform stages with the same mark compose. -/
theorem compose {total e₁ middle e₂ final : R} {mark : ℕ}
    (h₁ : Certificate total e₁ middle mark)
    (h₂ : Certificate middle e₂ final mark) :
    Certificate total (e₁ * e₂) final mark := by
  constructor
  rw [h₁.factorization, h₂.factorization, mul_pow]
  ring

/-- Multiplying the controlled transform by a unit-equivalent factor gives the
corresponding exact total-transform equality. -/
theorem change_controlled_by_unit {total exceptional controlled controlled' u : R}
    {mark : ℕ} (h : Certificate total exceptional controlled mark)
    (hu : controlled = u * controlled') :
    total = exceptional ^ mark * u * controlled' := by
  rw [h.factorization, hu]
  ring

/-- A unit controlled transform generates the unit ideal. -/
theorem span_controlled_eq_top {total exceptional controlled : R} {mark : ℕ}
    (_h : Certificate total exceptional controlled mark)
    (hu : IsUnit controlled) :
    Ideal.span ({controlled} : Set R) = ⊤ := by
  rw [Ideal.span_singleton_eq_top]
  exact hu

end Certificate

/-- A finite all-chart transform package. -/
structure ChartPackage (Chart : Type*) [Fintype Chart]
    (total : Chart → R) (exceptional : Chart → R)
    (controlled : Chart → R) (mark : ℕ) : Prop where
  certified : ∀ chart, Certificate (total chart) (exceptional chart)
    (controlled chart) mark

namespace ChartPackage

/-- Every chart in a finite transform package has the exact exceptional
factorization. -/
theorem factorization {Chart : Type*} [Fintype Chart]
    {total exceptional controlled : Chart → R} {mark : ℕ}
    (P : ChartPackage Chart total exceptional controlled mark) (chart : Chart) :
    total chart = exceptional chart ^ mark * controlled chart :=
  (P.certified chart).factorization

end ChartPackage

end PCRLean.Algebra.ControlledTransform
