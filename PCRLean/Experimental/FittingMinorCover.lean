import Mathlib

/-!
# Experimental finite Fitting-minor cover

A finite family of square minors defines a standard-open cover precisely when
their determinants generate the unit ideal.  This file packages that condition
and proves the pointwise covering statement: every prime ideal avoids at least
one determinant, hence belongs to at least one principal minor chart.

Combined with `FittingAwayRegularCentre`, every chart in such a cover carries a
local actual regular centre once the localized packet and test-vector data are
realized.  This file does not construct those localized data or glue their
ideals on overlaps.
-/

namespace PCRLean
namespace Experimental
namespace FittingMinorCover

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Finite family of square minors whose determinants generate the unit ideal. -/
structure Cover where
  minor : Chart → Matrix ι ι R
  span_det_eq_top :
    Ideal.span (Set.range fun c : Chart => (minor c).det) = ⊤

namespace Cover

variable (C : Cover (R := R) (Chart := Chart) (ι := ι))

/-- The determinant family is a finite subset of the coefficient ring. -/
theorem determinantSet_finite :
    (Set.range fun c : Chart => (C.minor c).det).Finite :=
  Set.finite_range _

/-- Every prime ideal avoids at least one determinant from the cover. -/
theorem exists_det_not_mem_prime
    (p : Ideal R) [p.IsPrime] :
    ∃ c : Chart, (C.minor c).det ∉ p := by
  by_contra h
  push_neg at h
  have hspan_le :
      Ideal.span (Set.range fun c : Chart => (C.minor c).det) ≤ p := by
    rw [Ideal.span_le]
    rintro x ⟨c, rfl⟩
    exact h c
  rw [C.span_det_eq_top] at hspan_le
  exact p.ne_top (top_unique hspan_le)

/-- Equivalent covering formulation: the common vanishing locus of all minor
determinants contains no prime ideal. -/
theorem not_all_det_mem_prime
    (p : Ideal R) [p.IsPrime] :
    ¬ ∀ c : Chart, (C.minor c).det ∈ p := by
  intro hall
  rcases C.exists_det_not_mem_prime p with ⟨c, hc⟩
  exact hc (hall c)

/-- No proper ideal can contain every determinant of the cover. -/
theorem exists_det_not_mem_of_ne_top
    (J : Ideal R) (hJ : J ≠ ⊤) :
    ∃ c : Chart, (C.minor c).det ∉ J := by
  by_contra h
  push_neg at h
  have hspan_le :
      Ideal.span (Set.range fun c : Chart => (C.minor c).det) ≤ J := by
    rw [Ideal.span_le]
    rintro x ⟨c, rfl⟩
    exact h c
  rw [C.span_det_eq_top] at hspan_le
  exact hJ (top_unique hspan_le)

end Cover

end

end FittingMinorCover
end Experimental
end PCRLean
