import Mathlib
import PCRLean.MonogenicFrobeniusFrame

/-!
# Concrete Frobenius frames on monogenic quotient algebras

For a positive integer `q` and `t : R`, the monogenic quotient

`A = R[X] / (X^q - t)`

has the canonical power basis `1, x, ..., x^(q-1)`. The adjoined root satisfies
`x^q = t`, so `MonogenicFrobeniusFrame` applies without any abstract frame
hypothesis. Consequently, an ideal of this concrete quotient algebra that is
stable under the finite transported Hasse operators descends exactly from the
base ring.

This file turns the finite coordinate calculation into an actual theorem about
`AdjoinRoot (X^q - C t)`. It is a concrete local algebra model for a finite
Frobenius chart.
-/

namespace PCRLean
namespace AdjoinRootFrobeniusFrame

noncomputable section

open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The monogenic Frobenius polynomial `X^q - t`. -/
def definingPolynomial (q : Nat) (t : R) : R[X] :=
  X ^ q - C t

/-- The defining polynomial is monic as soon as the exponent is positive. -/
theorem definingPolynomial_monic {q : Nat} (t : R) (hq : q ≠ 0) :
    (definingPolynomial (R := R) q t).Monic := by
  simpa [definingPolynomial] using
    (Polynomial.monic_X_pow_sub_C t hq)

/-- The canonical degree of the monogenic Frobenius polynomial. -/
@[simp] theorem definingPolynomial_natDegree [Nontrivial R]
    (q : Nat) (t : R) :
    (definingPolynomial (R := R) q t).natDegree = q := by
  simp [definingPolynomial]

/-- The adjoined root satisfies the declared monogenic relation. -/
theorem root_pow_eq_algebraMap (q : Nat) (t : R) :
    AdjoinRoot.root (definingPolynomial (R := R) q t) ^ q =
      algebraMap R (AdjoinRoot (definingPolynomial (R := R) q t)) t := by
  rw [AdjoinRoot.algebraMap_eq, ← sub_eq_zero,
    ← AdjoinRoot.eval₂_root,
    definingPolynomial, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

section Domain

variable [IsDomain R]

/-- The quotient by `X^q - t` is nontrivial when `q` is positive. -/
theorem definingPolynomial_degree_ne_zero
    {q : Nat} (t : R) (hq : 0 < q) :
    (definingPolynomial (R := R) q t).degree ≠ 0 := by
  have hg := definingPolynomial_monic (R := R) t hq.ne'
  rw [Polynomial.degree_eq_natDegree hg.ne_zero,
    definingPolynomial_natDegree]
  exact_mod_cast hq.ne'

/-- The canonical monogenic frame on `R[X]/(X^q-t)`. Its dimension is written
as the natural degree of the defining polynomial, which is propositionally
`q` by `definingPolynomial_natDegree`. -/
def frame (q : Nat) (t : R) (hq : 0 < q) :
    MonogenicFrobeniusFrame.Frame
      (R := R)
      (A := AdjoinRoot (definingPolynomial (R := R) q t))
      (definingPolynomial (R := R) q t).natDegree t := by
  have hg : (definingPolynomial (R := R) q t).Monic :=
    definingPolynomial_monic (R := R) t hq.ne'
  letI : Nontrivial (AdjoinRoot (definingPolynomial (R := R) q t)) :=
    AdjoinRoot.nontrivial _
      (definingPolynomial_degree_ne_zero (R := R) t hq)
  refine MonogenicFrobeniusFrame.ofPowerBasis
    (R := R)
    (A := AdjoinRoot (definingPolynomial (R := R) q t))
    (AdjoinRoot.powerBasis' hg) t ?_
  change AdjoinRoot.root (definingPolynomial (R := R) q t) ^
      (definingPolynomial (R := R) q t).natDegree =
    algebraMap R (AdjoinRoot (definingPolynomial (R := R) q t)) t
  rw [definingPolynomial_natDegree]
  exact root_pow_eq_algebraMap (R := R) q t

/-- Concrete Hasse-only ideal descent for the monogenic quotient
`R[X]/(X^q-t)`. -/
theorem ideal_eq_map_comap_of_hasse_stable
    (q : Nat) (t : R) (hq : 0 < q)
    (I : Ideal (AdjoinRoot (definingPolynomial (R := R) q t)))
    (hhasse : ∀ d : Fin (definingPolynomial (R := R) q t).natDegree,
      EndomorphismGeneration.StableUnder
        (IdealEndomorphismDescent.idealSubmodule (R := R) I)
        (CoordinatePacketDescent.pullbackOperator
          (frame (R := R) q t hq).coord
          (FiniteHasseModel.hasse
            (R := R)
            (definingPolynomial (R := R) q t).natDegree d))) :
    I = (I.comap
          (algebraMap R
            (AdjoinRoot (definingPolynomial (R := R) q t)))).map
        (algebraMap R
          (AdjoinRoot (definingPolynomial (R := R) q t))) := by
  exact (frame (R := R) q t hq).ideal_eq_map_comap_of_hasse_stable
    I hhasse

end Domain

end

end AdjoinRootFrobeniusFrame
end PCRLean
