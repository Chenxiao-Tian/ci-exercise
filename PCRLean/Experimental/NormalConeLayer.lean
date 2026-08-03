import Mathlib.LinearAlgebra.Quotient.Basic
import PCRLean.Experimental.GradedPowerReflection

/-!
# Normal-cone layers and initial-power nonvanishing

For an ideal `I`, the degree-`r` layer of its normal cone is the quotient
module

`I^r / I^(r+1)`.

This file constructs that quotient directly, defines the initial class of an
element `x ∈ I^r`, and proves that the class is zero exactly when
`x ∈ I^(r+1)`.

For a positive power `q`, define `InitialPowerNonvanishing q I` by requiring
that the `q`-th power of every nonzero initial class remains nonzero in degree
`q*r`.  This quotient-module formulation is proved equivalent to
`GradedPowerInjective q I`, the layer condition already known to imply full
root reflection in the `I`-adic filtration.

Thus reducedness of the normal cone can be connected to Frobenius-normality
without treating the associated graded ring as an informal metaphor.
-/

namespace PCRLean
namespace Experimental
namespace NormalConeLayer

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- The copy of `I^(r+1)` inside the module `I^r`. -/
def nextPowerSubmodule (I : Ideal A) (r : Nat) :
    Submodule A (I ^ r) :=
  (I ^ (r + 1)).comap (I ^ r).subtype

/-- Degree-`r` normal-cone layer `I^r / I^(r+1)`. -/
abbrev Layer (I : Ideal A) (r : Nat) :=
  (I ^ r) ⧸ nextPowerSubmodule I r

/-- Initial class of an element known to lie in `I^r`. -/
def initialClass
    (I : Ideal A) (r : Nat) (x : A) (hx : x ∈ I ^ r) :
    Layer I r :=
  Submodule.Quotient.mk ⟨x, hx⟩

/-- The initial class vanishes exactly one filtration step later. -/
theorem initialClass_eq_zero_iff
    (I : Ideal A) (r : Nat) (x : A) (hx : x ∈ I ^ r) :
    initialClass I r x hx = 0 ↔ x ∈ I ^ (r + 1) := by
  rw [initialClass, Submodule.Quotient.mk_eq_zero]
  rfl

/-- Nonvanishing formulation. -/
theorem initialClass_ne_zero_iff
    (I : Ideal A) (r : Nat) (x : A) (hx : x ∈ I ^ r) :
    initialClass I r x hx ≠ 0 ↔ x ∉ I ^ (r + 1) := by
  exact not_congr (initialClass_eq_zero_iff I r x hx)

/-- A power of an element in `I^r` lies in the correspondingly scaled power. -/
theorem pow_mem_scaled
    (I : Ideal A) (q r : Nat) {x : A} (hx : x ∈ I ^ r) :
    x ^ q ∈ I ^ (q * r) := by
  have hp : x ^ q ∈ (I ^ r) ^ q := Ideal.pow_mem_pow hx q
  simpa [pow_mul, Nat.mul_comm] using hp

/-- The `q`-th power of a nonzero initial form remains nonzero in the scaled
normal-cone layer. -/
def InitialPowerNonvanishing (q : Nat) (I : Ideal A) : Prop :=
  ∀ (r : Nat) (x : A) (hx : x ∈ I ^ r),
    initialClass I r x hx ≠ 0 →
      initialClass I (q * r) (x ^ q)
        (pow_mem_scaled I q r hx) ≠ 0

/-- Initial-power nonvanishing implies the algebraic one-layer reflection
condition. -/
theorem gradedPowerInjective_of_initialPowerNonvanishing
    (q : Nat) (I : Ideal A)
    (hinit : InitialPowerNonvanishing q I) :
    GradedPowerReflection.GradedPowerInjective q I := by
  intro r x hx hpowNext
  by_contra hxNext
  have hini : initialClass I r x hx ≠ 0 :=
    (initialClass_ne_zero_iff I r x hx).mpr hxNext
  have hpowIni := hinit r x hx hini
  have hzero :
      initialClass I (q * r) (x ^ q)
        (pow_mem_scaled I q r hx) = 0 :=
    (initialClass_eq_zero_iff I (q * r) (x ^ q)
      (pow_mem_scaled I q r hx)).mpr hpowNext
  exact hpowIni hzero

/-- Conversely, one-layer reflection says exactly that nonzero initial forms
have nonzero powers. -/
theorem initialPowerNonvanishing_of_gradedPowerInjective
    (q : Nat) (I : Ideal A)
    (hgraded : GradedPowerReflection.GradedPowerInjective q I) :
    InitialPowerNonvanishing q I := by
  intro r x hx hini
  rw [initialClass_ne_zero_iff] at hini ⊢
  intro hpowNext
  exact hini (hgraded r x hx hpowNext)

/-- Exact equivalence between quotient-layer and ideal-membership languages. -/
theorem initialPowerNonvanishing_iff_gradedPowerInjective
    (q : Nat) (I : Ideal A) :
    InitialPowerNonvanishing q I ↔
      GradedPowerReflection.GradedPowerInjective q I := by
  constructor
  · exact gradedPowerInjective_of_initialPowerNonvanishing q I
  · exact initialPowerNonvanishing_of_gradedPowerInjective q I

/-- Prime-power nonvanishing on every normal-cone layer implies full
Frobenius-normality. -/
theorem reflectsFrobeniusPowers_of_initialPowerNonvanishing
    (p : Nat) [Fact p.Prime] (I : Ideal A)
    (hinit : ∀ e : Nat, InitialPowerNonvanishing (p ^ e) I) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  apply GradedPowerReflection.reflectsFrobeniusPowers_of_frobeniusGradedReduced
  intro e
  exact gradedPowerInjective_of_initialPowerNonvanishing
    (p ^ e) I (hinit e)

end

end NormalConeLayer
end Experimental
end PCRLean
