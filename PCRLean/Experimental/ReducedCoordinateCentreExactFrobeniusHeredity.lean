import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.CoordinateBlowupChart
import PCRLean.Experimental.CoordinateCentreQuotient
import PCRLean.Experimental.FrobeniusNormalCentre
import PCRLean.Experimental.FrobeniusSupportReduced

/-!
# Reduced coefficient rings and exact coordinate-centre heredity

For a positive-dimensional coordinate centre, the passive variables form the
coefficient ring of the normal polynomial algebra.  The centre filtration
reflects prime-power roots exactly when that coefficient ring is reduced.

The forward direction is proved by the reduced-coefficient support theorem.
The converse is sharp: a nonzero nilpotent coefficient is a constant
polynomial outside the centre ideal whose prime power vanishes, and therefore
violates reflection.

Thus reducedness is not merely a convenient sufficient hypothesis for the
normal-cone argument.  In the coordinate model it is the exact obstruction.
This is the algebraic boundary needed by the proposed regular-centre theorem:
a regular centre has a reduced coordinate ring, while a nonreduced normal cone
can genuinely destroy Frobenius heredity.
-/

namespace PCRLean
namespace Experimental
namespace ReducedCoordinateCentreExactFrobeniusHeredity

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {α : Type v} {ι : Type w}
variable [DecidableEq α] [DecidableEq ι]

abbrev P := CoordinateBlowupChart.P (R := R) (α := α) (ι := ι)
abbrev Iterated := MvPolynomial ι (MvPolynomial α R)

/-- Put normal variables in the outer polynomial layer and passive variables
in the coefficient ring. -/
noncomputable def normalPolynomialEquiv :
    P (R := R) (α := α) (ι := ι) ≃ₐ[R]
      Iterated (R := R) (α := α) (ι := ι) :=
  (MvPolynomial.renameEquiv R (Equiv.sumComm α ι)).trans
    (MvPolynomial.sumAlgEquiv R ι α)

@[simp] theorem normalPolynomialEquiv_centreVar (i : ι) :
    normalPolynomialEquiv (R := R) (α := α) (ι := ι)
        (CoordinateBlowupChart.centreVar
          (R := R) (α := α) (ι := ι) i) =
      MvPolynomial.X i := by
  simp [normalPolynomialEquiv, CoordinateBlowupChart.centreVar]

@[simp] theorem normalPolynomialEquiv_passiveVar (a : α) :
    normalPolynomialEquiv (R := R) (α := α) (ι := ι)
        (CoordinateBlowupChart.passiveVar
          (R := R) (α := α) (ι := ι) a) =
      MvPolynomial.C (MvPolynomial.X a) := by
  simp [normalPolynomialEquiv, CoordinateBlowupChart.passiveVar]

/-- Full variable ideal in the normal polynomial layer. -/
def normalIdeal :
    Ideal (Iterated (R := R) (α := α) (ι := ι)) :=
  MvPolynomial.idealOfVars ι (MvPolynomial α R)

/-- The iterated polynomial equivalence sends the centre ideal exactly to the
normal full-variable ideal. -/
theorem map_centreIdeal_eq_normalIdeal :
    Ideal.map
        (normalPolynomialEquiv (R := R) (α := α) (ι := ι)).toAlgHom
        (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) =
      normalIdeal (R := R) (α := α) (ι := ι) := by
  apply le_antisymm
  · rw [CoordinateBlowupChart.centreIdeal, normalIdeal,
      MvPolynomial.idealOfVars, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap, normalPolynomialEquiv_centreVar]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [normalIdeal, MvPolynomial.idealOfVars, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [← normalPolynomialEquiv_centreVar
      (R := R) (α := α) (ι := ι) i]
    exact Ideal.mem_map_of_mem _
      (by
        rw [CoordinateBlowupChart.centreIdeal]
        exact Ideal.subset_span ⟨i, rfl⟩)

/-- The inverse equivalence sends the normal ideal back to the centre ideal. -/
theorem map_normalIdeal_eq_centreIdeal :
    Ideal.map
        (normalPolynomialEquiv (R := R) (α := α) (ι := ι)).symm.toAlgHom
        (normalIdeal (R := R) (α := α) (ι := ι)) =
      CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι) := by
  apply le_antisymm
  · rw [normalIdeal, MvPolynomial.idealOfVars,
      CoordinateBlowupChart.centreIdeal,
      Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simp
    rw [CoordinateBlowupChart.centreIdeal]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [CoordinateBlowupChart.centreIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (R := R) (α := α) (ι := ι)).symm.toAlgHom
      (Ideal.subset_span (s := Set.range (MvPolynomial.X : ι →
        Iterated (R := R) (α := α) (ι := ι))) ⟨i, rfl⟩)
    simpa using hm

/-- Exact ideal-power membership transport. -/
theorem mem_centreIdeal_pow_iff_normalIdeal_pow
    (f : P (R := R) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ^ mark ↔
      normalPolynomialEquiv (R := R) (α := α) (ι := ι) f ∈
        (normalIdeal (R := R) (α := α) (ι := ι)) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (R := R) (α := α) (ι := ι)).toAlgHom hf
    rw [Ideal.map_pow, map_centreIdeal_eq_normalIdeal] at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem
      (normalPolynomialEquiv (R := R) (α := α) (ι := ι)).symm.toAlgHom hf
    rw [Ideal.map_pow, map_normalIdeal_eq_centreIdeal] at hm
    simpa using hm

/-- Exact normal-order predicate in the iterated polynomial model. -/
def NormalOrderGE
    (f : P (R := R) (α := α) (ι := ι)) (mark : Nat) : Prop :=
  FrobeniusSupportReduced.OrderGE
    (normalPolynomialEquiv (R := R) (α := α) (ι := ι) f) mark

/-- Normal order is exactly actual centre-ideal power membership. -/
theorem mem_centreIdeal_pow_iff_normalOrderGE
    (f : P (R := R) (α := α) (ι := ι)) (mark : Nat) :
    f ∈ (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ^ mark ↔
      NormalOrderGE (R := R) (α := α) (ι := ι) f mark := by
  rw [mem_centreIdeal_pow_iff_normalIdeal_pow]
  change
    normalPolynomialEquiv (R := R) (α := α) (ι := ι) f ∈
        MvPolynomial.idealOfVars ι (MvPolynomial α R) ^ mark ↔
      ∀ d ∈ (normalPolynomialEquiv
        (R := R) (α := α) (ι := ι) f).support,
        mark ≤ InitialFormFrobeniusCleaning.exponentDegree d
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  simp [InitialFormFrobeniusCleaning.exponentDegree,
    Finsupp.degree_apply]

section Reduced

variable [IsReduced R]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Frobenius powers preserve exact normal order after scaling the mark over a
reduced coefficient ring. -/
theorem normalOrderGE_power_iff
    (e mark : Nat)
    (g : P (R := R) (α := α) (ι := ι)) :
    NormalOrderGE (R := R) (α := α) (ι := ι)
        (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      NormalOrderGE (R := R) (α := α) (ι := ι) g mark := by
  unfold NormalOrderGE
  rw [map_pow]
  exact FrobeniusSupportReduced.orderGE_power_iff
    p e mark (normalPolynomialEquiv
      (R := R) (α := α) (ι := ι) g)

/-- Main exact positive-dimensional centre heredity theorem over reduced
coefficients. -/
theorem frobeniusPower_mem_centreIdeal_pow_iff
    (e mark : Nat)
    (g : P (R := R) (α := α) (ι := ι)) :
    g ^ (p ^ e) ∈
        (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ^ ((p ^ e) * mark) ↔
      g ∈ (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ^ mark := by
  rw [mem_centreIdeal_pow_iff_normalOrderGE,
    mem_centreIdeal_pow_iff_normalOrderGE]
  exact normalOrderGE_power_iff p e mark g

/-- Reduced coefficients imply the abstract Frobenius-normal filtration
interface. -/
theorem coordinateCentre_reflects :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι)) := by
  intro e mark x hx
  exact (frobeniusPower_mem_centreIdeal_pow_iff
    (R := R) (α := α) (ι := ι) p e mark x).mp hx

end Reduced

section Necessity

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- If the coordinate-centre filtration reflects `p`-power roots, then the
coefficient ring is reduced. -/
theorem isReduced_of_coordinateCentre_reflects
    (hreflect : FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι))) :
    IsReduced R := by
  rw [isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt]
  intro a ha
  let x : P (R := R) (α := α) (ι := ι) := MvPolynomial.C a
  have hxpow :
      x ^ p ∈
        (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ^ p := by
    have hzero : x ^ p = 0 := by
      simp [x, ha]
    rw [hzero]
    exact Ideal.zero_mem _
  have hx :
      x ∈ CoordinateBlowupChart.centreIdeal
        (R := R) (α := α) (ι := ι) := by
    apply hreflect 1 1 x
    simpa using hxpow
  have hker := CoordinateCentreQuotient.centreIdeal_le_ker
    (K := R) (α := α) (ι := ι) hx
  have hzeroC := RingHom.mem_ker.mp hker
  have hCa : (MvPolynomial.C a : MvPolynomial α R) = 0 := by
    simpa [x] using hzeroC
  exact MvPolynomial.C_injective hCa

/-- Sharp characterization: the coordinate-centre filtration is
Frobenius-normal exactly when the coefficient ring is reduced. -/
theorem coordinateCentre_reflects_iff_isReduced :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p
        (CoordinateBlowupChart.centreIdeal
          (R := R) (α := α) (ι := ι)) ↔
      IsReduced R := by
  constructor
  · exact isReduced_of_coordinateCentre_reflects
      (R := R) (α := α) (ι := ι) p
  · intro hred
    letI : IsReduced R := hred
    exact coordinateCentre_reflects
      (R := R) (α := α) (ι := ι) p

end Necessity

end

end ReducedCoordinateCentreExactFrobeniusHeredity
end Experimental
end PCRLean
