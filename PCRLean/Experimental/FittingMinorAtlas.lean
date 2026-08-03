import Mathlib
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Experimental finite Fitting-minor atlas

A finite family of determinant minors gives a global constant-rank atlas once
those determinants generate the unit ideal. Equivalently, their basic open
subsets cover the whole prime spectrum. On the chart obtained by localizing
away from one determinant, that determinant is automatically a unit.

This turns the pointwise phrase "choose an invertible minor" into a finite,
executable cover certificate. The next layer attaches actual conormal/graph
data to each localization and compiles the local graph-centre macro.
-/

namespace PCRLean
namespace Experimental
namespace FittingMinorAtlas

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]

/-- A finite family of candidate minors whose determinants generate the unit
ideal. -/
structure Atlas where
  determinant : Chart → R
  cover : Ideal.span (Set.range determinant) = ⊤

namespace Atlas

variable (A : Atlas (R := R) (Chart := Chart))

/-- The determinant basic opens cover all of `Spec R`. -/
theorem basicOpen_cover :
    (⨆ c : Chart, PrimeSpectrum.basicOpen (A.determinant c)) = ⊤ := by
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr A.cover

/-- Every proper ideal misses at least one determinant. -/
theorem exists_determinant_not_mem
    (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ c : Chart, A.determinant c ∉ I := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range A.determinant) ≤ I := by
    rw [Ideal.span_le]
    rintro x ⟨c, rfl⟩
    exact h c
  rw [A.cover] at hle
  exact hI (top_unique hle)

/-- Every prime point belongs to one determinant chart. -/
theorem point_mem_some_basicOpen (x : PrimeSpectrum R) :
    ∃ c : Chart, x ∈ PrimeSpectrum.basicOpen (A.determinant c) := by
  rcases A.exists_determinant_not_mem x.asIdeal x.isPrime.ne_top with ⟨c, hc⟩
  exact ⟨c, PrimeSpectrum.mem_basicOpen.mpr hc⟩

/-- The selected determinant becomes a unit in every away localization. -/
theorem determinant_isUnit_of_isLocalizationAway
    (c : Chart)
    (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away (A.determinant c) S] :
    IsUnit (algebraMap R S (A.determinant c)) := by
  let y : Submonoid.powers (A.determinant c) :=
    ⟨A.determinant c, ⟨1, by simp⟩⟩
  exact IsLocalization.map_units S y

/-- Unit certificate in the canonical away localization. -/
theorem determinant_isUnit_away (c : Chart) :
    IsUnit
      (algebraMap R (Localization.Away (A.determinant c))
        (A.determinant c)) := by
  exact A.determinant_isUnit_of_isLocalizationAway
    c (Localization.Away (A.determinant c))

/-- The localization chart realizes exactly its determinant basic open. -/
theorem localization_range_eq_basicOpen (c : Chart) :
    Set.range
        (PrimeSpectrum.comap
          (algebraMap R (Localization.Away (A.determinant c)))) =
      (PrimeSpectrum.basicOpen (A.determinant c) : Set (PrimeSpectrum R)) := by
  exact PrimeSpectrum.localization_away_comap_range
    (Localization.Away (A.determinant c)) (A.determinant c)

end Atlas

end

end FittingMinorAtlas
end Experimental
end PCRLean
