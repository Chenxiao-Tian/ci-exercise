import Mathlib
import PCRLean.FrobeniusGaugeRelation

/-!
# Gauge-invariant operator orbits

If a linear observation kills the image of the cleaning operator, then it takes
the same value on gauge-equivalent presentations.  When the Hasse--Cartier
operator family commutes with cleaning, every finite descendant has the same
projected value.  Thus a packet built in the quotient by cleaning is genuinely
presentation invariant.
-/

namespace PCRLean
namespace GaugeInvariantOrbit

noncomputable section

universe u v w x

variable {R : Type u} {M : Type v} {N : Type w} {ι : Type x}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- A projected observation is cleaning-invariant when it annihilates the
image of the gauge operator. -/
def KillsGauge (F : Module.End R M) (q : M →ₗ[R] N) : Prop :=
  q.comp F = 0

/-- A gauge-killing observation has equal values on gauge-equivalent
presentations. -/
theorem map_eq_of_gauge
    (F : Module.End R M) (q : M →ₗ[R] N)
    (hkill : KillsGauge F q)
    {x y : M} (hxy : FrobeniusGaugeRelation.GaugeEquivalent F x y) :
    q x = q y := by
  rcases hxy with ⟨g, hg⟩
  have hzero := congrArg (fun L : M →ₗ[R] N => L g) hkill
  change q (F g) = 0 at hzero
  have hdiff : q (x - y) = 0 := by
    rw [← hg]
    exact hzero
  rw [map_sub, sub_eq_zero] at hdiff
  exact hdiff

/-- Every finite compatible operator descendant of two gauge-equivalent seeds
has the same projected value. -/
theorem applyWord_map_eq
    (F : Module.End R M) (ops : ι → Module.End R M)
    (hcompat : FrobeniusGaugeRelation.FamilyCompatible F ops)
    (q : M →ₗ[R] N) (hkill : KillsGauge F q)
    (word : List ι) {x y : M}
    (hxy : FrobeniusGaugeRelation.GaugeEquivalent F x y) :
    q (FrobeniusGaugeRelation.applyWord ops word x) =
      q (FrobeniusGaugeRelation.applyWord ops word y) := by
  apply map_eq_of_gauge F q hkill
  exact FrobeniusGaugeRelation.applyWord_preserves F ops hcompat word hxy

/-- Cleaning the seed by one gauge image leaves every projected finite
operator descendant unchanged. -/
theorem cleaned_seed_applyWord_map_eq
    (F : Module.End R M) (ops : ι → Module.End R M)
    (hcompat : FrobeniusGaugeRelation.FamilyCompatible F ops)
    (q : M →ₗ[R] N) (hkill : KillsGauge F q)
    (word : List ι) (seed gauge : M) :
    q (FrobeniusGaugeRelation.applyWord ops word (seed + F gauge)) =
      q (FrobeniusGaugeRelation.applyWord ops word seed) := by
  exact applyWord_map_eq F ops hcompat q hkill word
    (FrobeniusGaugeRelation.add_image F seed gauge)

/-- The set of all projected finite descendants is exactly unchanged by
cleaning the seed. -/
theorem projected_orbitSet_eq
    (F : Module.End R M) (ops : ι → Module.End R M)
    (hcompat : FrobeniusGaugeRelation.FamilyCompatible F ops)
    (q : M →ₗ[R] N) (hkill : KillsGauge F q)
    (seed gauge : M) :
    {z : N | ∃ word : List ι,
      z = q (FrobeniusGaugeRelation.applyWord ops word (seed + F gauge))} =
    {z : N | ∃ word : List ι,
      z = q (FrobeniusGaugeRelation.applyWord ops word seed)} := by
  ext z
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨word, cleaned_seed_applyWord_map_eq F ops hcompat q hkill word seed gauge⟩
  · rintro ⟨word, rfl⟩
    exact ⟨word,
      (cleaned_seed_applyWord_map_eq F ops hcompat q hkill word seed gauge).symm⟩

end

end GaugeInvariantOrbit
end PCRLean
