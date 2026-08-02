import Mathlib

/-!
# Principal ideals glued by unit cocycles

Equality of local names is not a gluing theorem.  For a principal centre or
branch ideal, the correct overlap certificate is multiplication by a unit.
This file proves that such a certificate gives equality of the generated
ideals and packages a finite unit-cocycle atlas in one ambient ring.

The theorem is an algebraic overlap lemma.  A scheme-level application still
has to supply the localization maps and verify the cocycle on actual overlaps.
-/

namespace PCRLean.Algebra.UnitCocycleIdeal

variable {R : Type*} [CommRing R]

/-- Multiplying a generator by a unit does not change its principal ideal. -/
theorem span_singleton_unit_mul (u : Rˣ) (g : R) :
    Ideal.span ({(u : R) * g} : Set R) = Ideal.span ({g} : Set R) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    intro x hx
    have hx' : x = (u : R) * g := by simpa using hx
    rw [hx']
    exact (Ideal.span ({g} : Set R)).mul_mem_left (u : R)
      (Ideal.subset_span (by simp))
  · refine Ideal.span_le.mpr ?_
    intro x hx
    have hx' : x = g := by simpa using hx
    rw [hx']
    have hgen : (u : R) * g ∈ Ideal.span ({(u : R) * g} : Set R) :=
      Ideal.subset_span (by simp)
    have hinv := (Ideal.span ({(u : R) * g} : Set R)).mul_mem_left
      ((↑(u⁻¹) : R)) hgen
    simpa using hinv

/-- Unit-related local generators define the same principal ideal. -/
theorem span_singleton_eq_of_eq_unit_mul {f g : R} (u : Rˣ)
    (h : f = (u : R) * g) :
    Ideal.span ({f} : Set R) = Ideal.span ({g} : Set R) := by
  rw [h]
  exact span_singleton_unit_mul u g

/-- A finite family of local principal generators with explicit unit
transition functions.  The cocycle equations themselves are recorded because
they are needed for a coherent atlas, although ideal equality only uses the
pairwise compatibility equation. -/
structure PrincipalUnitAtlas (Chart : Type*) where
  generator : Chart → R
  transition : Chart → Chart → Rˣ
  compatible : ∀ i j, generator i = (transition i j : R) * generator j
  transition_refl : ∀ i, transition i i = 1
  transition_cocycle : ∀ i j k, transition i j * transition j k = transition i k

namespace PrincipalUnitAtlas

variable {Chart : Type*} (A : PrincipalUnitAtlas (R := R) Chart)

/-- Every two chart generators in a unit-cocycle atlas generate the same
ideal. -/
theorem ideal_eq (i j : Chart) :
    Ideal.span ({A.generator i} : Set R) =
      Ideal.span ({A.generator j} : Set R) :=
  span_singleton_eq_of_eq_unit_mul (A.transition i j) (A.compatible i j)

/-- Choosing a reference chart produces a chart-independent principal ideal. -/
def gluedIdeal (i : Chart) : Ideal R :=
  Ideal.span ({A.generator i} : Set R)

/-- The ideal obtained from any reference chart is independent of that
reference. -/
theorem gluedIdeal_eq (i j : Chart) : A.gluedIdeal i = A.gluedIdeal j :=
  A.ideal_eq i j

end PrincipalUnitAtlas

end PCRLean.Algebra.UnitCocycleIdeal
