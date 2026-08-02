import Mathlib
import Mathlib.RingTheory.Ideal.Lattice

/-!
# Canonical differential-operator saturation of an ideal

A presentation-independent packet should depend on an ideal rather than on a
chosen list of generators. Given any family of additive operators on a
commutative ring, this file defines the least ideal containing a seed ideal and
stable under every operator. The definition is an intersection, so no choice
of generators or order of closure operations is retained. On a Noetherian
ring the resulting actual ideal is finitely generated.

For Hasse--Schmidt or Cartier applications, a separate theorem must show that
the relevant operators on transformed charts are represented by the declared
family and that this saturation carries the required marked degree data.
-/

namespace PCRLean
namespace DifferentialIdealSaturation

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- Stability of an ideal under a family of additive operators. -/
def Stable (ops : ι → R →+ R) (J : Ideal R) : Prop :=
  ∀ i x, x ∈ J → ops i x ∈ J

/-- Ideals containing the seed and stable under every declared operator. -/
def admissible (ops : ι → R →+ R) (I : Ideal R) : Set (Ideal R) :=
  {J | I ≤ J ∧ Stable ops J}

/-- The least operator-stable ideal containing the seed. -/
def saturation (ops : ι → R →+ R) (I : Ideal R) : Ideal R :=
  sInf (admissible ops I)

/-- The unit ideal is always operator-stable. -/
theorem stable_top (ops : ι → R →+ R) : Stable ops (⊤ : Ideal R) := by
  intro i x hx
  trivial

/-- The admissible family is nonempty. -/
theorem admissible_nonempty (ops : ι → R →+ R) (I : Ideal R) :
    (admissible ops I).Nonempty := by
  exact ⟨⊤, le_top, stable_top ops⟩

/-- The seed ideal is contained in its canonical saturation. -/
theorem le_saturation (ops : ι → R →+ R) (I : Ideal R) :
    I ≤ saturation ops I := by
  intro x hx
  rw [saturation, Ideal.mem_sInf]
  intro J hJ
  exact hJ.1 hx

/-- The canonical saturation is stable under every declared operator. -/
theorem saturation_stable (ops : ι → R →+ R) (I : Ideal R) :
    Stable ops (saturation ops I) := by
  intro i x hx
  rw [saturation, Ideal.mem_sInf] at hx ⊢
  intro J hJ
  exact hJ.2 i x (hx hJ)

/-- Minimality of canonical saturation. -/
theorem saturation_le_of_le_of_stable
    (ops : ι → R →+ R) {I J : Ideal R}
    (hIJ : I ≤ J) (hJ : Stable ops J) :
    saturation ops I ≤ J := by
  unfold saturation
  exact sInf_le ⟨hIJ, hJ⟩

/-- Characterization by the universal property among stable ideals. -/
theorem saturation_le_iff
    (ops : ι → R →+ R) {I J : Ideal R}
    (hJ : Stable ops J) :
    saturation ops I ≤ J ↔ I ≤ J := by
  constructor
  · intro h
    exact (le_saturation ops I).trans h
  · intro h
    exact saturation_le_of_le_of_stable ops h hJ

/-- Saturation is monotone in the seed ideal. -/
theorem saturation_mono (ops : ι → R →+ R)
    {I J : Ideal R} (hIJ : I ≤ J) :
    saturation ops I ≤ saturation ops J := by
  apply saturation_le_of_le_of_stable ops
  · exact hIJ.trans (le_saturation ops J)
  · exact saturation_stable ops J

/-- An already stable ideal is fixed by saturation. -/
theorem saturation_eq_self_of_stable
    (ops : ι → R →+ R) (I : Ideal R)
    (hI : Stable ops I) :
    saturation ops I = I := by
  apply le_antisymm
  · exact saturation_le_of_le_of_stable ops le_rfl hI
  · exact le_saturation ops I

/-- Canonical saturation is idempotent. -/
theorem saturation_idempotent
    (ops : ι → R →+ R) (I : Ideal R) :
    saturation ops (saturation ops I) = saturation ops I := by
  exact saturation_eq_self_of_stable ops (saturation ops I)
    (saturation_stable ops I)

/-- Equal seed ideals have equal saturations; no generating frame survives. -/
theorem saturation_congr (ops : ι → R →+ R)
    {I J : Ideal R} (h : I = J) :
    saturation ops I = saturation ops J := by
  subst J
  rfl

/-- Adding more declared operators can only enlarge the canonical saturated
ideal. -/
theorem saturation_mono_operators
    {κ : Type*} (ops : ι → R →+ R) (more : κ → R →+ R)
    (embed : ι → κ) (hcompat : ∀ i, more (embed i) = ops i)
    (I : Ideal R) :
    saturation ops I ≤ saturation more I := by
  apply saturation_le_of_le_of_stable ops
  · exact le_saturation more I
  · intro i x hx
    rw [← hcompat i]
    exact saturation_stable more I (embed i) x hx

section Noetherian

variable [IsNoetherianRing R]

/-- On a Noetherian ring, the canonical operator saturation is an actual
finitely generated ideal. -/
theorem saturation_fg (ops : ι → R →+ R) (I : Ideal R) :
    (saturation ops I).FG :=
  IsNoetherian.noetherian _

/-- A finite set of actual ring elements generates the canonical saturation. -/
theorem exists_finite_generators (ops : ι → R →+ R) (I : Ideal R) :
    ∃ s : Finset R, saturation ops I = Ideal.span (s : Set R) := by
  rcases saturation_fg ops I with ⟨s, hs⟩
  exact ⟨s, hs.symm⟩

end Noetherian

end

end DifferentialIdealSaturation
end PCRLean
