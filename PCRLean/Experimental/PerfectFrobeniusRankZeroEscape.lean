import Mathlib
import PCRLean.LinearPacketIdeal
import PCRLean.FunctionalPacketIdeal
import PCRLean.Experimental.DualPacketRankZeroNoGo

/-!
# Experimental perfect-field Frobenius escape from rank zero

Over a perfect field of characteristic `p`, every coefficient admits an
iterated `p^e`-th root.  A pure Frobenius form

`∑ i, a i * X_i^(p^e)`

therefore has a canonical linear Frobenius root.  The `p^e`-th power of that
linear polynomial is exactly the original pure form.  If the pure form is
nonzero, the recovered covector is nonzero, and the singleton covector packet
has positive row-span rank.

Thus a rank-zero first-order packet can reenter the positive-rank linear chamber
whenever the higher diagnostic layer supplies a nonzero pure Frobenius form.
This theorem does not prove that every quasilinear singularity supplies such a
form or handle imperfect residue fields.
-/

namespace PCRLean
namespace Experimental
namespace PerfectFrobeniusRankZeroEscape

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]
variable (p : Nat) [Fact p.Prime] [CharP K p] [PerfectField K p]

abbrev Direction := σ → K
abbrev Dual := Module.Dual K (Direction (K := K) (σ := σ))

/-- Iterated inverse Frobenius on coefficients. -/
noncomputable def frobeniusRootIter : Nat → K → K
  | 0, a => a
  | e + 1, a => (frobeniusEquiv K p).symm (frobeniusRootIter p e a)

/-- The iterated inverse is a genuine `p^e`-th root. -/
theorem frobeniusRootIter_pow (e : Nat) (a : K) :
    (frobeniusRootIter p e a) ^ (p ^ e) = a := by
  induction e with
  | zero => simp [frobeniusRootIter]
  | succ e ih =>
      have hstep :
          (frobeniusRootIter p (e + 1) a) ^ p =
            frobeniusRootIter p e a := by
        simp [frobeniusRootIter]
      rw [pow_succ, Nat.mul_comm, pow_mul, hstep, ih]

/-- Finite sums commute with `p^e`-th powers. -/
theorem finset_sum_pow_char_pow
    {A : Type*} [CommRing A] [CharP A p]
    {ι : Type*} (s : Finset ι) (f : ι → A) (e : Nat) :
    (∑ i ∈ s, f i) ^ (p ^ e) = ∑ i ∈ s, (f i) ^ (p ^ e) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [pow_pos (Fact.out : p.Prime).pos e]
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, add_pow_char_pow, ih]

/-- The pure Frobenius polynomial attached to a coefficient row. -/
def pureFrobeniusPolynomial
    (coeff : σ → K) (e : Nat) : MvPolynomial σ K :=
  ∑ i : σ, MvPolynomial.C (coeff i) *
    (MvPolynomial.X i) ^ (p ^ e)

/-- Coefficientwise linear Frobenius root. -/
def rootRow (coeff : σ → K) (e : Nat) : σ → K :=
  fun i => frobeniusRootIter p e (coeff i)

/-- Linear polynomial recovered from the higher Frobenius form. -/
def rootLinearPolynomial
    (coeff : σ → K) (e : Nat) : MvPolynomial σ K :=
  LinearPacketIdeal.linearPolynomial (rootRow p coeff e)

/-- Exact Frobenius-root identity. -/
theorem rootLinearPolynomial_pow
    (coeff : σ → K) (e : Nat) :
    (rootLinearPolynomial p coeff e) ^ (p ^ e) =
      pureFrobeniusPolynomial p coeff e := by
  classical
  rw [rootLinearPolynomial, LinearPacketIdeal.linearPolynomial,
    pureFrobeniusPolynomial]
  rw [finset_sum_pow_char_pow p Finset.univ
    (fun i => MvPolynomial.C (rootRow p coeff e i) * MvPolynomial.X i) e]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_pow, rootRow, frobeniusRootIter_pow]

/-- Covector represented by the recovered root row. -/
def rootFunctional
    (coeff : σ → K) (e : Nat) : Dual (K := K) (σ := σ) where
  toFun x := ∑ i : σ, rootRow p coeff e i * x i
  map_add' := by
    intro x y
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

/-- The coefficient row of the recovered covector is the Frobenius root row. -/
theorem coefficientRow_rootFunctional
    (coeff : σ → K) (e : Nat) :
    FunctionalPacketIdeal.coefficientRow (rootFunctional p coeff e) =
      rootRow p coeff e := by
  classical
  funext j
  simp [FunctionalPacketIdeal.coefficientRow,
    FunctionalPacketIdeal.basisVector, rootFunctional]

/-- Integrating the recovered covector gives the recovered linear polynomial. -/
theorem functionalPolynomial_rootFunctional
    (coeff : σ → K) (e : Nat) :
    FunctionalPacketIdeal.functionalPolynomial (rootFunctional p coeff e) =
      rootLinearPolynomial p coeff e := by
  rw [FunctionalPacketIdeal.functionalPolynomial,
    coefficientRow_rootFunctional, rootLinearPolynomial]

/-- The singleton recovered covector packet. -/
def rootPacket
    (coeff : σ → K) (e : Nat) : Unit → Dual (K := K) (σ := σ) :=
  fun _ => rootFunctional p coeff e

/-- A nonzero pure Frobenius form has a nonzero recovered covector. -/
theorem rootFunctional_ne_zero_of_pure_ne_zero
    (coeff : σ → K) (e : Nat)
    (hpure : pureFrobeniusPolynomial p coeff e ≠ 0) :
    rootFunctional p coeff e ≠ 0 := by
  intro hzero
  have hpoly : rootLinearPolynomial p coeff e = 0 := by
    rw [← functionalPolynomial_rootFunctional]
    rw [hzero]
    simp [FunctionalPacketIdeal.functionalPolynomial,
      FunctionalPacketIdeal.coefficientRow,
      LinearPacketIdeal.linearPolynomial]
  apply hpure
  rw [← rootLinearPolynomial_pow p coeff e, hpoly]
  simp [pow_pos (Fact.out : p.Prime).pos e]

/-- A nonzero pure Frobenius form produces a positive-rank covector packet. -/
theorem rootPacket_positive_finrank
    (coeff : σ → K) (e : Nat)
    (hpure : pureFrobeniusPolynomial p coeff e ≠ 0) :
    0 < FiniteDimensional.finrank K
      (DualPacketRegularCentre.packetSpan (rootPacket p coeff e)) := by
  have hfun := rootFunctional_ne_zero_of_pure_ne_zero p coeff e hpure
  apply Nat.pos_of_ne_zero
  intro hzero
  have hz := DualPacketRankZeroNoGo.packet_eq_zero_of_finrank_eq_zero
    (rootPacket p coeff e) hzero Unit.unit
  exact hfun hz

/-- The recovered positive-rank packet has a nonempty pivot chart type. -/
theorem rootPacket_hasPivot
    (coeff : σ → K) (e : Nat)
    (hpure : pureFrobeniusPolynomial p coeff e ≠ 0) :
    Nonempty
      (DualPacketCoordinateNormalization.CentreIndex
        (rootPacket p coeff e)) :=
  DualPacketBlowupChart.nonempty_centreIndex_of_positive_finrank
    p (rootPacket p coeff e)
    (rootPacket_positive_finrank p coeff e hpure)

end

end PerfectFrobeniusRankZeroEscape
end Experimental
end PCRLean
