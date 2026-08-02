import Mathlib

/-!
# Finite source and birth-carrier bounds

The finite-source termination chamber does not merely label events.  It
requires an injective payment map from financed births to a fixed finite
ancestor carrier, and a source representative that is not shared by two
simultaneously active identities.  The elementary cardinal bounds below are
the exact combinatorial consequences of those geometric certificates.
-/

namespace PCRLean.Termination.FiniteSources

/-- Financed births are bounded by a fixed finite carrier whenever every birth
consumes a distinct carrier coupon. -/
theorem financed_birth_bound
    {Birth Coupon : Type*} [Fintype Birth] [Fintype Coupon]
    (pay : Birth → Coupon) (hpay : Function.Injective pay) :
    Fintype.card Birth ≤ Fintype.card Coupon :=
  Fintype.card_le_of_injective pay hpay

/-- The same bound in finite-set form. -/
theorem financed_birth_finset_bound
    {Birth Coupon : Type*} [DecidableEq Coupon]
    (births : Finset Birth) (pay : Birth → Coupon)
    (hpay : Set.InjOn pay births) :
    (births.image pay).card = births.card := by
  exact Finset.card_image_iff.mpr hpay

/-- Active identities are bounded by a finite source universe whenever each
active identity owns a distinguished source and those sources are distinct. -/
theorem active_identity_bound
    {Identity Source : Type*} [Fintype Identity] [Fintype Source]
    (representative : Identity → Source)
    (hrep : Function.Injective representative) :
    Fintype.card Identity ≤ Fintype.card Source :=
  Fintype.card_le_of_injective representative hrep

/-- No infinite sequence can inject into a finite coupon type. -/
theorem no_infinite_financed_births
    {Coupon : Type*} [Finite Coupon] (pay : ℕ → Coupon) :
    ¬ Function.Injective pay := by
  intro hpay
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite pay
  exact hij (hpay heq)

/-- A finite source universe alone does not justify source splitting or
cloning; injectivity is precisely the additional invariant used by the bound. -/
theorem clone_breaks_injectivity
    {Identity Source : Type*} {i j : Identity} {s : Source}
    (hij : i ≠ j) (representative : Identity → Source)
    (hi : representative i = s) (hj : representative j = s) :
    ¬ Function.Injective representative := by
  intro hinj
  exact hij (hinj (hi.trans hj.symm))

end PCRLean.Termination.FiniteSources
