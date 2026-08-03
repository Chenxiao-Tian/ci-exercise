import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.CoordinateBlowupChart
import PCRLean.Experimental.CoordinateSubspaceOrderHeredity
import PCRLean.Experimental.FrobeniusSupportDomain

/-!
# Exact Frobenius heredity for positive-dimensional coordinate centres

Swap the passive and normal variable blocks and use the standard iterated
polynomial equivalence

`K[x,z] ≃ (K[x])[z]`.

Under this equivalence the positive-dimensional coordinate-centre ideal
`(z_i)` becomes the full variable ideal in the normal polynomial ring over the
passive coefficient domain.  Mathlib's exact characterization of powers of the
full variable ideal then identifies centre order with actual ideal-power
membership in both directions.

Since Frobenius support scaling is valid over coefficient domains, not only
fields, one obtains the exact reflection theorem

`g^(p^e) ∈ I^((p^e)*m) ↔ g ∈ I^m`.

This is the affine split-coordinate model of graded differential heredity for a
regular positive-dimensional centre.  Scheme localization, arbitrary regular
immersions, nonprincipal Rees presentations, passive owners and transforms are
still open.
-/

namespace PCRLean
namespace Experimental
namespace CoordinateCentreExactFrobeniusHeredity

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {α : Type v} {ι : Type w}
variable [DecidableEq α] [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := K) (α := α) (ι := ι)
abbrev Iterated := MvPolynomial ι (MvPolynomial α K)

/-- Put the normal variables in the outer polynomial layer and the passive
variables in the coefficient ring. -/
noncomputable def normalPolynomialEquiv :
    P (K := K) (α := α) (ι := ι) ≃ₐ[K]
      Iterated (K := K) (α := α) (ι := ι) :=
  (MvPolynomial.renameEquiv K (Equiv.sumComm α ι)).trans
    (MvPolynomial.sumAlgEquiv K ι α)

@[simp] theorem normalPolynomialEquiv_centreVar (i : ι) :
    normalPolynomialEquiv (K := K) (α := α) (ι := ι)
        (CoordinateBlowupChart.centreVar
          (R := K) (α := α) (ι := ι) i) =
      MvPolynomial.X i := by
  simp [normalPolynomialEquiv, CoordinateBlowupChart.centreVar]

@[simp] theorem normalPolynomialEquiv_passiveVar (a : α) :
    normalPolynomialEquiv (K := K) (α := α) (ι := ι)
        (CoordinateBlowupChart.passiveVar
          (R := K) (α := α) (ι := ι) a) =
      MvPolynomial.C (MvPolynomial.X a) := by
  simp [normalPolynomialEquiv, CoordinateBlowupChart.passiveVar]

/-- Full variable ideal in the normal polynomial layer. -/
def normalIdeal :
    Ideal (Iterated (K := K) (α := α) (ι := ι)) :=
  MvPolynomial.idealOfVars ι (MvPolynomial α K)

/-- The iterated polynomial equivalence sends the centre ideal exactly to the
normal full-variable ideal. -/
theorem map_centreIdeal_eq_normalIdeal :
    Ideal.map
        (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).toAlgHom
        (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) =
      normalIdeal (K := K) (α := α) (ι := ι) := by
  apply le_antisymm
  · rw [CoordinateBlowupChart.centreIdeal, normalIdeal,
      MvPolynomial.idealOfVars, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap, normalPolynomialEquiv_centreVar]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [normalIdeal, MvPolynomial.idealOfVars, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [← normalPolynomialEquiv_centreVar (K := K) (α := α) (ι := ι) i]
    exact Ideal.mem_map_of_mem _
      (CoordinateSubspaceOrderHeredity.centreVar_mem
        (K := K) (α := α) i)

/-- The inverse equivalence sends the normal ideal back to the coordinate
centre ideal. -/
theorem map_normalIdeal_eq_centreIdeal :
    Ideal.map
        (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).symm.toAlgHom
        (normalIdeal (K := K) (α := α) (ι := ι)) =
      CoordinateBlowupChart.centreIdeal
        (R := K) (α := α) (ι := ι) := by
  apply le_antisymm
  · rw [normalIdeal, MvPolynomial.idealOfVars,
      CoordinateBlowupChart.centreIdeal,
      Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simp
    exact CoordinateSubspaceOrderHeredity.centreVar_mem
      (K := K) (α := α) i
  · rw [CoordinateBlowupChart.centreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).symm.toAlgHom
      (Ideal.subset_span (s := Set.range (MvPolynomial.X : ι →
        Iterated (K := K) (α := α) (ι := ι))) ⟨i, rfl⟩)
    simpa using hm

/-- Every centre-ideal power is transported exactly. -/
theorem map_centreIdeal_pow_eq_normalIdeal_pow (mark : Nat) :
    Ideal.map
        (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).toAlgHom
        ((CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark) =
      (normalIdeal (K := K) (α := α) (ι := ι)) ^ mark := by
  rw [Ideal.map_pow, map_centreIdeal_eq_normalIdeal]

/-- Exact ideal-power membership transport. -/
theorem mem_centreIdeal_pow_iff_normalIdeal_pow
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark ↔
      normalPolynomialEquiv (K := K) (α := α) (ι := ι) f ∈
        (normalIdeal (K := K) (α := α) (ι := ι)) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).toAlgHom hf
    rw [map_centreIdeal_pow_eq_normalIdeal_pow] at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (K := K) (α := α) (ι := ι)).symm.toAlgHom hf
    rw [Ideal.map_pow, map_normalIdeal_eq_centreIdeal] at hm
    simpa using hm

/-- Exact normal-order predicate in the iterated polynomial model. -/
def NormalOrderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) : Prop :=
  FrobeniusSupportDomain.OrderGE
    (normalPolynomialEquiv (K := K) (α := α) (ι := ι) f) mark

/-- Normal order is exactly actual centre-ideal power membership. -/
theorem mem_centreIdeal_pow_iff_normalOrderGE
    (f : P (K := K) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark ↔
      NormalOrderGE (K := K) (α := α) (ι := ι) f mark := by
  rw [mem_centreIdeal_pow_iff_normalIdeal_pow]
  change
    normalPolynomialEquiv (K := K) (α := α) (ι := ι) f ∈
        MvPolynomial.idealOfVars ι (MvPolynomial α K) ^ mark ↔
      ∀ d ∈ (normalPolynomialEquiv
        (K := K) (α := α) (ι := ι) f).support,
        mark ≤ InitialFormFrobeniusCleaning.exponentDegree d
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  simp [InitialFormFrobeniusCleaning.exponentDegree,
    Finsupp.degree_apply]

/-- Frobenius powers preserve exact normal order after scaling the mark. -/
theorem normalOrderGE_power_iff
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι)) :
    NormalOrderGE (K := K) (α := α) (ι := ι)
        (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      NormalOrderGE (K := K) (α := α) (ι := ι) g mark := by
  unfold NormalOrderGE
  rw [map_pow]
  exact FrobeniusSupportDomain.orderGE_power_iff
    p e mark (normalPolynomialEquiv (K := K) (α := α) (ι := ι) g)

/-- Main exact positive-dimensional centre heredity theorem. -/
theorem frobeniusPower_mem_centreIdeal_pow_iff
    (p : Nat) [Fact p.Prime] [CharP K p]
    (e mark : Nat)
    (g : P (K := K) (α := α) (ι := ι)) :
    g ^ (p ^ e) ∈
        (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ ((p ^ e) * mark) ↔
      g ∈ (CoordinateBlowupChart.centreIdeal
          (R := K) (α := α) (ι := ι)) ^ mark := by
  rw [mem_centreIdeal_pow_iff_normalOrderGE,
    mem_centreIdeal_pow_iff_normalOrderGE]
  exact normalOrderGE_power_iff p e mark g

end

end CoordinateCentreExactFrobeniusHeredity
end Experimental
end PCRLean
