import Mathlib
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PCRLean.Experimental.ReducedGraphCentreQuotient
import PCRLean.Experimental.ReducedPolynomialGraphCentreHeredity

/-!
# Faithfully flat descent of graph-centre quotient data

For a faithfully flat algebra `A → B`, the natural map

`A/I → B/IB`

is injective.  Hence reducedness of the extended centre quotient descends to
`A/I`.  If the extended ideal is an actual polynomial graph ideal, its
properness also forces the original ideal to be proper.

Together with the previously proved Frobenius-filtration descent, this retains
three essential pieces of the local centre certificate after fpqc descent:

* nonidentity of the centre;
* reducedness of the centre coordinate ring; and
* exact marked Frobenius reflection.

Regularity and finite locally free conormal descent remain separate bridge
obligations.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatGraphCentreDescent

noncomputable section

universe u v w x

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Natural map from a quotient to the quotient by the extended ideal. -/
def quotientMap (I : Ideal A) :
    A ⧸ I →+* B ⧸ I.map (algebraMap A B) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (I.map (algebraMap A B))).comp (algebraMap A B))
    (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_map_of_mem (algebraMap A B) ha)

@[simp] theorem quotientMap_mk (I : Ideal A) (a : A) :
    quotientMap (B := B) I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a) := by
  rfl

/-- Faithful flatness makes the quotient base-change map injective. -/
theorem quotientMap_injective (I : Ideal A) :
    Function.Injective (quotientMap (B := B) I) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have htarget :
      Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a) =
        Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B b) := by
    simpa using hxy
  have hzero :
      Ideal.Quotient.mk (I.map (algebraMap A B))
          (algebraMap A B (a - b)) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr htarget
  have hmemMap :
      algebraMap A B (a - b) ∈ I.map (algebraMap A B) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [← sub_eq_zero, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have heq := Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I
  rw [← heq]
  exact hmemMap

/-- Reducedness of the quotient descends along the faithfully flat extension. -/
theorem quotient_isReduced_of_extended
    (I : Ideal A)
    [IsReduced (B ⧸ I.map (algebraMap A B))] :
    IsReduced (A ⧸ I) :=
  isReduced_of_injective
    (quotientMap (B := B) I)
    (quotientMap_injective (B := B) I)

section GraphModel

variable {R : Type w} [CommRing R] [Nontrivial R] [IsReduced R]
variable {ι : Type x} [Finite ι] [DecidableEq ι]

abbrev GraphRing := MvPolynomial ι R

variable [Algebra A (GraphRing (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (GraphRing (R := R) (ι := ι))]

open ReducedPolynomialGraphCentreHeredity

/-- A faithfully flat graph model forces the original centre to be proper. -/
theorem ideal_ne_top_of_graphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : I.map (algebraMap A (GraphRing (R := R) (ι := ι))) =
      graphIdeal h) :
    I ≠ ⊤ := by
  intro htop
  have hmapTop :
      I.map (algebraMap A (GraphRing (R := R) (ι := ι))) = ⊤ := by
    rw [htop]
    simp
  apply ReducedGraphCentreQuotient.graphIdeal_ne_top h
  rw [← hmodel, hmapTop]

/-- A reduced polynomial graph model makes the original centre quotient
reduced. -/
theorem quotient_isReduced_of_graphModel
    (I : Ideal A) (h : ι → R)
    (hmodel : I.map (algebraMap A (GraphRing (R := R) (ι := ι))) =
      graphIdeal h) :
    IsReduced (A ⧸ I) := by
  let J : Ideal (GraphRing (R := R) (ι := ι)) :=
    I.map (algebraMap A (GraphRing (R := R) (ι := ι)))
  let e :
      (GraphRing (R := R) (ι := ι) ⧸ J) ≃+*
        (GraphRing (R := R) (ι := ι) ⧸ graphIdeal h) :=
    Ideal.quotEquivOfEq hmodel
  letI : IsReduced (GraphRing (R := R) (ι := ι) ⧸ graphIdeal h) :=
    ReducedGraphCentreQuotient.quotient_isReduced h
  letI : IsReduced (GraphRing (R := R) (ι := ι) ⧸ J) :=
    isReduced_of_injective e.toRingHom e.injective
  exact quotient_isReduced_of_extended
    (B := GraphRing (R := R) (ι := ι)) I

end GraphModel

end

end FaithfullyFlatGraphCentreDescent
end Experimental
end PCRLean
