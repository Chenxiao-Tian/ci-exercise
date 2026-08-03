import Mathlib
import PCRLean.Experimental.UnivariateFrobeniusOrderHeredity
import PCRLean.Experimental.UnivariateOrderBaseChange
import PCRLean.Experimental.FrobeniusMarkScalingBoundary

/-!
# Universal marked Frobenius equivalence

Bare integral equivalence forgets the grading and is therefore too weak for
resolution. The correct local principal relation remembers the mark and tests
the singular condition after every faithful coefficient extension.

Two marked equations are universally marked-equivalent if, after every
injective map to a field in the chosen universe, they have the same marked
singular condition at every rational point of the target field. Prime-power
root compression is universally marked-equivalent precisely when the mark is
scaled by the same prime power. The coordinate example proves that omitting
this mark scaling destroys universal equivalence.

This is a one-variable principal model for the proposed graded integral
closure class of a differential Rees algebra. The scheme-level theory must
replace rational-point order by local order at arbitrary primes and include
nonprincipal finite presentations, differential saturation and transforms.
-/

namespace PCRLean
namespace Experimental
namespace UniversalMarkedFrobeniusEquivalence

noncomputable section

universe u v w

variable {K : Type u} [Field K]

open UnivariateFrobeniusOrderHeredity

/-- Universal pointwise equivalence of two marked principal equations under
faithful coefficient-field extension. -/
def Equivalent
    (f : K[X]) (m : Nat) (g : K[X]) (n : Nat) : Prop :=
  ∀ (L : Type v) [Field L] (φ : K →+* L),
    Function.Injective φ → ∀ a : L,
      AtPointSingular a (f.map φ) m ↔
        AtPointSingular a (g.map φ) n

namespace Equivalent

/-- Reflexivity. -/
theorem refl (f : K[X]) (m : Nat) : Equivalent (v := v) f m f m := by
  intro L inst φ hφ a
  exact Iff.rfl

/-- Symmetry. -/
theorem symm {f g : K[X]} {m n : Nat}
    (h : Equivalent (v := v) f m g n) :
    Equivalent (v := v) g n f m := by
  intro L inst φ hφ a
  exact (h L φ hφ a).symm

/-- Transitivity. -/
theorem trans {f g h : K[X]} {m n r : Nat}
    (hfg : Equivalent (v := v) f m g n)
    (hgh : Equivalent (v := v) g n h r) :
    Equivalent (v := v) f m h r := by
  intro L inst φ hφ a
  exact (hfg L φ hφ a).trans (hgh L φ hφ a)

end Equivalent

/-- Prime-power compression is universally marked-equivalent after scaling the
mark. -/
theorem pow_equivalent
    (q mark : Nat) (hq : 0 < q) (g : K[X]) :
    Equivalent (v := v) (g ^ q) (q * mark) g mark := by
  intro L inst φ hφ a
  rw [Polynomial.map_pow]
  exact UnivariateFrobeniusOrderHeredity.atPointSingular_pow_iff
    q mark hq a (g.map φ)

/-- An explicit root identity yields universal marked equivalence. -/
theorem root_equivalent
    (q mark : Nat) (hq : 0 < q)
    {f g : K[X]} (hroot : g ^ q = f) :
    Equivalent (v := v) f (q * mark) g mark := by
  rw [← hroot]
  exact pow_equivalent (v := v) q mark hq g

/-- A weighted indexed principal presentation is universally equivalent after
simultaneous prime-power compression. -/
theorem family_pow_equivalent
    {κ : Type w}
    (q : Nat) (hq : 0 < q)
    (root : κ → K[X]) (mark : κ → Nat) :
    ∀ (L : Type v) [Field L] (φ : K →+* L),
      Function.Injective φ → ∀ a : L,
      (∀ j, AtPointSingular a (((root j) ^ q).map φ) (q * mark j)) ↔
        (∀ j, AtPointSingular a ((root j).map φ) (mark j)) := by
  intro L inst φ hφ a
  constructor
  · intro h j
    rw [Polynomial.map_pow] at h
    exact (UnivariateFrobeniusOrderHeredity.atPointSingular_pow_iff
      q (mark j) hq a ((root j).map φ)).mp (h j)
  · intro h j
    rw [Polynomial.map_pow]
    exact (UnivariateFrobeniusOrderHeredity.atPointSingular_pow_iff
      q (mark j) hq a ((root j).map φ)).mpr (h j)

/-- Without dividing the mark, even `X^q` and `X` fail universal marked
equivalence when `q > 1`. Thus bare integral equivalence cannot be the state
relation used by resolution. -/
theorem unscaled_coordinate_not_equivalent
    (q : Nat) (hq : 1 < q) :
    ¬ Equivalent (v := u)
      ((Polynomial.X : K[X]) ^ q) q (Polynomial.X : K[X]) q := by
  intro h
  have hiff := h K (RingHom.id K) Function.injective_id 0
  have hleft :
      AtPointSingular 0 ((Polynomial.X : K[X]) ^ q) q := by
    simpa [AtPointSingular] using
      FrobeniusMarkScalingBoundary.X_pow_singular_at_scaled_mark
        (K := K) q (lt_trans Nat.zero_lt_one hq)
  have hright :
      ¬ AtPointSingular 0 (Polynomial.X : K[X]) q := by
    simpa [AtPointSingular] using
      FrobeniusMarkScalingBoundary.X_not_singular_at_unscaled_mark
        (K := K) q hq
  exact hright (hiff.mp hleft)

section Perfect

variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- Canonical perfect-field extraction of a derivative-zero equation is a
universal marked equivalence after dividing its mark by `p`. -/
theorem derivativeZero_root_equivalent
    (mark : Nat) (f : K[X])
    (hderiv : Polynomial.derivative f = 0) :
    Equivalent (v := v) f (p * mark)
      (PolynomialFrobeniusExtraction.frobeniusRoot p f) mark := by
  apply root_equivalent (v := v) p mark (Fact.out : p.Prime).pos
  exact PolynomialFrobeniusExtraction.frobeniusRoot_pow_eq p f hderiv

end Perfect

end

end UniversalMarkedFrobeniusEquivalence
end Experimental
end PCRLean
