import Mathlib
import Mathlib.RingTheory.Flat.Basic
import PCRLean.Experimental.PolynomialGraphCentreHeredity

/-!
# Induced-flat passive safety for polynomial graph centres

Let `P = R[Z_i]` and let `I_h = (Z_i-h_i)` be a polynomial graph centre.
For an `R`-flat passive module `N`, consider the induced ambient module

`M = P ⊗[R] N`.

The tensor-product flatness instance makes `M` flat over `P`.  Consequently
tensoring any injective `P`-linear relation with `M` stays injective.  In
particular, for the graph ideal and every one of its powers, the maps

`I_h^n ⊗[P] M → P ⊗[P] M`

are injective.  This is the exact `Tor₁`-vanishing gate for induced-flat passive
data along the graph centre.

The result does not cover arbitrary passive modules.  It isolates a large,
functorial chamber in which passive safety follows from an actual module
construction rather than being inferred from active marked containment.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphPassiveSafety

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable [Module.Flat R N]

open PolynomialGraphCentreHeredity

abbrev P := MvPolynomial ι R

/-- Passive module induced from the coefficient ring. -/
abbrev InducedPassive : Type max u v w :=
  P (R := R) (ι := ι) ⊗[R] N

/-- The induced passive module is flat over the ambient polynomial ring. -/
theorem inducedPassive_flat :
    Module.Flat (P (R := R) (ι := ι))
      (InducedPassive (R := R) (ι := ι) (N := N)) := by
  infer_instance

/-- Tensor-injectivity formulation of the first Tor-vanishing gate. -/
def TorOneSafeAlong
    (I : Ideal (P (R := R) (ι := ι))) : Prop :=
  Function.Injective
    (I.subtype.rTensor
      (InducedPassive (R := R) (ι := ι) (N := N)))

/-- Flatness gives the Tor gate for every ambient ideal. -/
theorem torOneSafeAlong_allIdeals
    (I : Ideal (P (R := R) (ι := ι))) :
    TorOneSafeAlong (R := R) (ι := ι) (N := N) I := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    I.subtype Subtype.val_injective

/-- In particular the polynomial graph centre is Tor-safe. -/
theorem graphIdeal_torOneSafe
    (h : ι → R) :
    TorOneSafeAlong (R := R) (ι := ι) (N := N)
      (graphIdeal h) :=
  torOneSafeAlong_allIdeals (R := R) (ι := ι) (N := N)
    (graphIdeal h)

/-- Every power of the graph-centre ideal is Tor-safe. -/
theorem graphIdeal_pow_torOneSafe
    (h : ι → R) (n : Nat) :
    TorOneSafeAlong (R := R) (ι := ι) (N := N)
      ((graphIdeal h) ^ n) :=
  torOneSafeAlong_allIdeals (R := R) (ι := ι) (N := N)
    ((graphIdeal h) ^ n)

/-- More generally, every injective passive relation remains injective after
base change to the induced passive module. -/
theorem preserves_injective_relation
    {M₁ : Type x} {M₂ : Type y}
    [AddCommGroup M₁] [Module (P (R := R) (ι := ι)) M₁]
    [AddCommGroup M₂] [Module (P (R := R) (ι := ι)) M₂]
    (f : M₁ →ₗ[P (R := R) (ι := ι)] M₂)
    (hf : Function.Injective f) :
    Function.Injective
      (f.rTensor (InducedPassive (R := R) (ι := ι) (N := N))) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- A compact passive-safety certificate for one graph centre. -/
structure Certificate (h : ι → R) where
  flat : Module.Flat (P (R := R) (ι := ι))
    (InducedPassive (R := R) (ι := ι) (N := N))
  graphTorSafe :
    TorOneSafeAlong (R := R) (ι := ι) (N := N) (graphIdeal h)
  allPowerTorSafe : ∀ n : Nat,
    TorOneSafeAlong (R := R) (ι := ι) (N := N)
      ((graphIdeal h) ^ n)

/-- Assemble the induced-flat passive certificate. -/
noncomputable def certificate (h : ι → R) :
    Certificate (R := R) (ι := ι) (N := N) h where
  flat := inducedPassive_flat (R := R) (ι := ι) (N := N)
  graphTorSafe := graphIdeal_torOneSafe
    (R := R) (ι := ι) (N := N) h
  allPowerTorSafe := graphIdeal_pow_torOneSafe
    (R := R) (ι := ι) (N := N) h

end

end PolynomialGraphPassiveSafety
end Experimental
end PCRLean
