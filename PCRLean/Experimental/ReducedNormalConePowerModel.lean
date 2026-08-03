import Mathlib
import PCRLean.Experimental.FrobeniusSupportReduced
import PCRLean.Experimental.NormalConeLayer

/-!
# Reduced normal-cone power models

The quotient layers `I^r / I^(r+1)` are presently available in the project,
but mathlib does not yet supply the full associated graded ring interface needed
by the resolution proof.  This file isolates the exact missing structure.

A `PowerModel q I` embeds every normal-cone layer into one reduced commutative
ring and requires compatibility between the initial class of `x^q` in degree
`q*r` and the `q`-th power of the encoded initial class of `x` in degree `r`.
Injectivity and reducedness then force nonzero initial classes to retain
nonzero `q`-th powers.

Thus a family of such models for `q = p^e` implies Frobenius-normality of the
entire `I`-adic filtration.  A future quasi-regular associated-graded theorem
only has to construct this model; the filtration induction and root reflection
are already compiled here.
-/

namespace PCRLean
namespace Experimental
namespace ReducedNormalConePowerModel

noncomputable section

universe u v

variable {A : Type u} [CommRing A]

/-- A reduced target faithfully encoding all normal-cone layers and their
`q`-th power operation. -/
structure PowerModel (q : Nat) (I : Ideal A) where
  G : Type v
  commRing : CommRing G
  reduced : IsReduced G
  encode : (r : Nat) → NormalConeLayer.Layer I r →+ G
  encode_injective : ∀ r, Function.Injective (encode r)
  encode_power : ∀ (r : Nat) (x : A) (hx : x ∈ I ^ r),
    encode (q * r)
        (NormalConeLayer.initialClass I (q * r) (x ^ q)
          (NormalConeLayer.pow_mem_scaled I q r hx)) =
      (encode r (NormalConeLayer.initialClass I r x hx)) ^ q

namespace PowerModel

variable {q : Nat} {I : Ideal A}
variable (M : PowerModel.{u, v} q I)

/-- A nonzero layer class has nonzero encoding. -/
theorem encode_ne_zero
    (r : Nat) (z : NormalConeLayer.Layer I r) (hz : z ≠ 0) :
    M.encode r z ≠ 0 := by
  intro hzero
  apply hz
  apply M.encode_injective r
  simpa using hzero

/-- Every reduced power model gives initial-power nonvanishing. -/
theorem initialPowerNonvanishing
    (hq : 0 < q) : NormalConeLayer.InitialPowerNonvanishing q I := by
  letI : CommRing M.G := M.commRing
  letI : IsReduced M.G := M.reduced
  intro r x hx hini
  let sourceClass := NormalConeLayer.initialClass I r x hx
  let targetClass := NormalConeLayer.initialClass I (q * r) (x ^ q)
    (NormalConeLayer.pow_mem_scaled I q r hx)
  have hsource : M.encode r sourceClass ≠ 0 := by
    exact M.encode_ne_zero r sourceClass hini
  have hsourcePow : (M.encode r sourceClass) ^ q ≠ 0 :=
    FrobeniusSupportReduced.pow_ne_zero_of_isReduced hsource hq
  intro htarget
  have hencodedTarget : M.encode (q * r) targetClass = 0 := by
    have h := congrArg (M.encode (q * r)) htarget
    simpa using h
  have hcompat :
      M.encode (q * r) targetClass =
        (M.encode r sourceClass) ^ q := by
    simpa [sourceClass, targetClass] using M.encode_power r x hx
  rw [hcompat] at hencodedTarget
  exact hsourcePow hencodedTarget

/-- The one-layer graded reflection condition follows from a reduced power
model. -/
theorem gradedPowerInjective
    (hq : 0 < q) :
    GradedPowerReflection.GradedPowerInjective q I :=
  NormalConeLayer.gradedPowerInjective_of_initialPowerNonvanishing
    q I (M.initialPowerNonvanishing hq)

end PowerModel

/-- A reduced model for every prime-power operation makes the full filtration
Frobenius-normal. -/
theorem reflectsFrobeniusPowers_of_models
    (p : Nat) [Fact p.Prime] (I : Ideal A)
    (model : ∀ e : Nat, PowerModel.{u, v} (p ^ e) I) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  apply NormalConeLayer.reflectsFrobeniusPowers_of_initialPowerNonvanishing
    p I
  intro e
  exact (model e).initialPowerNonvanishing
    (pow_pos (Fact.out : p.Prime).pos e)

end

end ReducedNormalConePowerModel
end Experimental
end PCRLean
