import Mathlib
import Mathlib.RingTheory.Regular.RegularSequence
import PCRLean.Experimental.PolynomialGraphCentreQuotient

/-!
# Boundary regular sequences on polynomial graph centres

Let `Q_h = R[Z_i]/(Z_i-h_i)`.  Evaluation gives a ring equivalence

`Q_h ≃+* R`.

For a list of boundary equations `r₁, …, rₙ` in `R`, let their restrictions to
the graph centre be the classes of the constant polynomials `C r_j` in `Q_h`.
This file proves that weak regularity and regularity of the sequence are
preserved and reflected exactly by the quotient equivalence.

Thus an ordered normal-crossings boundary sequence in the coefficient ring
remains the same regular sequence on the graph centre.  Combined with the exact
stratum quotient theorem, this supplies both the regular-strata and
non-zero-divisor components of the local SNC gate.

The result is affine and ordered-sequence based.  A complete scheme-level SNC
certificate must additionally glue local sequences up to units and
permutations and track divisor identities through every blowup chart.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphBoundaryRegularSequence

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]

open PolynomialGraphCentreHeredity
open PolynomialGraphCentreQuotient

abbrev P := MvPolynomial ι R
abbrev Q (h : ι → R) := P (R := R) (ι := ι) ⧸ graphIdeal h

/-- Restriction of a coefficient equation to the graph centre. -/
def restrictEquation
    (h : ι → R) (r : R) : Q (R := R) h :=
  Ideal.Quotient.mk (graphIdeal h) (MvPolynomial.C r)

/-- Restriction of an ordered boundary sequence. -/
def restrictSequence
    (h : ι → R) (rs : List R) : List (Q (R := R) h) :=
  rs.map (restrictEquation h)

@[simp] theorem quotientEquiv_restrictEquation
    (h : ι → R) (r : R) :
    quotientEquiv h (restrictEquation h r) = r := by
  simp [restrictEquation]

/-- Scalar multiplication by a restricted boundary equation is transported to
ordinary multiplication by the coefficient equation. -/
theorem quotientEquiv_smul_restrictEquation
    (h : ι → R) (r : R) (x : Q (R := R) h) :
    quotientEquiv h (restrictEquation h r • x) =
      r • quotientEquiv h x := by
  change quotientEquiv h (restrictEquation h r * x) =
    r * quotientEquiv h x
  rw [map_mul]
  simp

/-- The restricted and original sequences satisfy the scalar compatibility
relation required by regular-sequence transport. -/
theorem sequence_forall₂
    (h : ι → R) (rs : List R) :
    List.Forall₂
      (fun (q : Q (R := R) h) (r : R) =>
        ∀ x, (quotientEquiv h).toAddEquiv (q • x) =
          r • (quotientEquiv h).toAddEquiv x)
      (restrictSequence h rs) rs := by
  induction rs with
  | nil => exact List.Forall₂.nil
  | cons r rs ih =>
      apply List.Forall₂.cons
      · intro x
        exact quotientEquiv_smul_restrictEquation h r x
      · exact ih

/-- Weak regularity is preserved and reflected by restriction to the graph
centre. -/
theorem isWeaklyRegular_restrict_iff
    (h : ι → R) (rs : List R) :
    RingTheory.Sequence.IsWeaklyRegular
        (Q (R := R) h) (restrictSequence h rs) ↔
      RingTheory.Sequence.IsWeaklyRegular R rs := by
  exact (quotientEquiv h).toAddEquiv.isWeaklyRegular_congr
    (sequence_forall₂ h rs)

/-- Main SNC-sequence transport theorem. -/
theorem isRegular_restrict_iff
    (h : ι → R) (rs : List R) :
    RingTheory.Sequence.IsRegular
        (Q (R := R) h) (restrictSequence h rs) ↔
      RingTheory.Sequence.IsRegular R rs := by
  exact (quotientEquiv h).toAddEquiv.isRegular_congr
    (sequence_forall₂ h rs)

/-- A regular coefficient boundary sequence remains regular on the graph
centre. -/
theorem isRegular_restrict
    (h : ι → R) {rs : List R}
    (hrs : RingTheory.Sequence.IsRegular R rs) :
    RingTheory.Sequence.IsRegular
      (Q (R := R) h) (restrictSequence h rs) :=
  (isRegular_restrict_iff h rs).mpr hrs

/-- Conversely, regularity can be tested after restriction to the graph
centre. -/
theorem isRegular_of_restrict
    (h : ι → R) {rs : List R}
    (hrs : RingTheory.Sequence.IsRegular
      (Q (R := R) h) (restrictSequence h rs)) :
    RingTheory.Sequence.IsRegular R rs :=
  (isRegular_restrict_iff h rs).mp hrs

end

end PolynomialGraphBoundaryRegularSequence
end Experimental
end PCRLean
