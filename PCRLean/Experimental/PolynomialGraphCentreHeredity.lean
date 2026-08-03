import Mathlib
import Mathlib.RingTheory.MvPolynomial.Ideal
import PCRLean.Experimental.FrobeniusSupportDomain
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Polynomial graph centres and Frobenius heredity

Let `R` be a domain and let `h_i ∈ R`. In `R[Z_i]`, the equations

`Z_i - h_i = 0`

cut out the graph of the tuple `h`. Translation `Z_i ↦ Z_i + h_i` is a
polynomial automorphism carrying this graph ideal to the coordinate ideal
`(Z_i)`. Consequently all ideal powers, order predicates and prime-power
Frobenius compression laws transport from the coordinate centre to the graph
centre.

The main theorem is

`g^(p^e) ∈ I_h^((p^e)m) ↔ g ∈ I_h^m`.

When `R` is itself a passive polynomial ring, this treats nonlinear
positive-dimensional polynomial graph centres. It is the local algebraic form
expected after an étale graph presentation of a regular immersion.
-/

namespace PCRLean
namespace Experimental
namespace PolynomialGraphCentreHeredity

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι : Type v} [DecidableEq ι]

abbrev P := MvPolynomial ι R

/-- Translation by a coefficient-valued graph. -/
def translate (h : ι → R) : P (R := R) (ι := ι) →ₐ[R] P :=
  MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (h i)

@[simp] theorem translate_X (h : ι → R) (i : ι) :
    translate h (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (h i) := by
  simp [translate]

@[simp] theorem translate_C (h : ι → R) (r : R) :
    translate h (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [translate]

/-- Translation by `h` and `-h` are inverse. -/
theorem translate_comp_neg (h : ι → R) :
    (translate h).comp (translate (-h)) =
      AlgHom.id R (P (R := R) (ι := ι)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translate]

/-- The opposite composition is also the identity. -/
theorem translate_neg_comp (h : ι → R) :
    (translate (-h)).comp (translate h) =
      AlgHom.id R (P (R := R) (ι := ι)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [translate]

/-- Translation as an algebra automorphism. -/
noncomputable def translateEquiv (h : ι → R) :
    P (R := R) (ι := ι) ≃ₐ[R] P :=
  AlgEquiv.ofAlgHom (translate h) (translate (-h))
    (translate_comp_neg h) (translate_neg_comp h)

/-- One graph equation. -/
def graphGenerator (h : ι → R) (i : ι) : P (R := R) (ι := ι) :=
  MvPolynomial.X i - MvPolynomial.C (h i)

/-- Actual ideal of the graph. -/
def graphIdeal (h : ι → R) : Ideal (P (R := R) (ι := ι)) :=
  Ideal.span (Set.range (graphGenerator h))

/-- Coordinate ideal at the zero graph. -/
def originIdeal : Ideal (P (R := R) (ι := ι)) :=
  MvPolynomial.idealOfVars ι R

/-- Every graph equation belongs to the graph ideal. -/
theorem graphGenerator_mem (h : ι → R) (i : ι) :
    graphGenerator h i ∈ graphIdeal h :=
  Ideal.subset_span ⟨i, rfl⟩

/-- Translation sends a graph equation to a coordinate. -/
@[simp] theorem translate_graphGenerator (h : ι → R) (i : ι) :
    translate h (graphGenerator h i) = MvPolynomial.X i := by
  simp [translate, graphGenerator]

/-- Inverse translation sends a coordinate to a graph equation. -/
@[simp] theorem translate_neg_X (h : ι → R) (i : ι) :
    translate (-h) (MvPolynomial.X i) = graphGenerator h i := by
  simp [translate, graphGenerator]

/-- Translation carries the graph ideal exactly to the coordinate ideal. -/
theorem map_graphIdeal_eq_originIdeal (h : ι → R) :
    Ideal.map (translate h) (graphIdeal h) =
      originIdeal (R := R) (ι := ι) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, graphIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simpa [originIdeal] using
      (Ideal.subset_span ⟨i, rfl⟩ :
        MvPolynomial.X i ∈ MvPolynomial.idealOfVars ι R)
  · rw [originIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem (translate h)
      (graphGenerator_mem h i)
    simpa using hm

/-- Inverse translation carries the coordinate ideal back to the graph ideal. -/
theorem map_originIdeal_eq_graphIdeal (h : ι → R) :
    Ideal.map (translate (-h)) (originIdeal (R := R) (ι := ι)) =
      graphIdeal h := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, originIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [Ideal.mem_comap]
    simpa using graphGenerator_mem h i
  · rw [graphIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    have hXi : MvPolynomial.X i ∈ originIdeal (R := R) (ι := ι) :=
      Ideal.subset_span ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem (translate (-h)) hXi
    simpa using hm

/-- Translation carries all graph-ideal powers to coordinate-ideal powers. -/
theorem map_graphIdeal_pow_eq_originIdeal_pow
    (h : ι → R) (mark : Nat) :
    Ideal.map (translate h) ((graphIdeal h) ^ mark) =
      (originIdeal (R := R) (ι := ι)) ^ mark := by
  rw [Ideal.map_pow, map_graphIdeal_eq_originIdeal]

/-- Inverse translation carries coordinate powers back to graph powers. -/
theorem map_originIdeal_pow_eq_graphIdeal_pow
    (h : ι → R) (mark : Nat) :
    Ideal.map (translate (-h))
        ((originIdeal (R := R) (ι := ι)) ^ mark) =
      (graphIdeal h) ^ mark := by
  rw [Ideal.map_pow, map_originIdeal_eq_graphIdeal]

/-- Exact transport of marked-power membership. -/
theorem mem_graphIdeal_pow_iff
    (h : ι → R) (f : P (R := R) (ι := ι)) (mark : Nat) :
    f ∈ (graphIdeal h) ^ mark ↔
      translate h f ∈ (originIdeal (R := R) (ι := ι)) ^ mark := by
  constructor
  · intro hf
    have hm := Ideal.mem_map_of_mem (translate h) hf
    rw [map_graphIdeal_pow_eq_originIdeal_pow] at hm
    exact hm
  · intro hf
    have hm := Ideal.mem_map_of_mem (translate (-h)) hf
    rw [map_originIdeal_pow_eq_graphIdeal_pow] at hm
    have hvalue : translate (-h) (translate h f) = f := by
      have hcomp := congrArg
        (fun H : P (R := R) (ι := ι) →ₐ[R] P => H f)
        (translate_neg_comp h)
      simpa [AlgHom.comp_apply] using hcomp
    rw [← hvalue]
    exact hm

/-- Normal order along the graph centre. -/
def GraphOrderGE
    (h : ι → R) (f : P (R := R) (ι := ι)) (mark : Nat) : Prop :=
  FrobeniusSupportDomain.OrderGE (translate h f) mark

/-- Graph-centre ideal powers are exactly graph-normal order. -/
theorem mem_graphIdeal_pow_iff_graphOrderGE
    (h : ι → R) (f : P (R := R) (ι := ι)) (mark : Nat) :
    f ∈ (graphIdeal h) ^ mark ↔ GraphOrderGE h f mark := by
  rw [mem_graphIdeal_pow_iff, originIdeal,
    MvPolynomial.mem_pow_idealOfVars_iff]
  change
    (∀ d ∈ (translate h f).support, mark ≤ Finsupp.degree d) ↔
      ∀ d ∈ (translate h f).support,
        mark ≤ InitialFormFrobeniusCleaning.exponentDegree d
  simp [InitialFormFrobeniusCleaning.exponentDegree,
    Finsupp.degree_apply]

/-- Frobenius compression preserves order along a polynomial graph centre. -/
theorem graphOrderGE_power_iff
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e mark : Nat) (h : ι → R) (g : P (R := R) (ι := ι)) :
    GraphOrderGE h (g ^ (p ^ e)) ((p ^ e) * mark) ↔
      GraphOrderGE h g mark := by
  unfold GraphOrderGE
  rw [map_pow]
  exact FrobeniusSupportDomain.orderGE_power_iff p e mark
    (translate h g)

/-- Main graph-centre heredity theorem. -/
theorem frobeniusPower_mem_graphIdeal_pow_iff
    (p : Nat) [Fact p.Prime] [CharP R p]
    (e mark : Nat) (h : ι → R) (g : P (R := R) (ι := ι)) :
    g ^ (p ^ e) ∈ (graphIdeal h) ^ ((p ^ e) * mark) ↔
      g ∈ (graphIdeal h) ^ mark := by
  rw [mem_graphIdeal_pow_iff_graphOrderGE,
    mem_graphIdeal_pow_iff_graphOrderGE]
  exact graphOrderGE_power_iff p e mark h g

/-- The graph ideal has a Frobenius-normal filtration. -/
theorem graphIdeal_reflectsFrobeniusPowers
    (p : Nat) [Fact p.Prime] [CharP R p]
    (h : ι → R) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p (graphIdeal h) := by
  intro e mark g hg
  exact (frobeniusPower_mem_graphIdeal_pow_iff
    p e mark h g).mp hg

/-- The graph ideal is a genuine proper ideal. -/
theorem graphIdeal_ne_top (h : ι → R) : graphIdeal h ≠ ⊤ := by
  intro htop
  have hone : (1 : P (R := R) (ι := ι)) ∈ graphIdeal h := by
    rw [htop]
    trivial
  have hm := Ideal.mem_map_of_mem (translate h) hone
  rw [map_graphIdeal_eq_originIdeal] at hm
  have hnot : (1 : P (R := R) (ι := ι)) ∉
      originIdeal (R := R) (ι := ι) := by
    rw [originIdeal, ← pow_one,
      MvPolynomial.C_mem_pow_idealOfVars_iff]
    simp
  exact hnot (by simpa using hm)

/-- Over a Noetherian coefficient ring with finitely many normal variables, the
actual graph ideal is finitely generated. -/
theorem graphIdeal_fg
    [IsNoetherianRing R] [Finite ι] (h : ι → R) :
    (graphIdeal h).FG :=
  IsNoetherian.noetherian _

end

end PolynomialGraphCentreHeredity
end Experimental
end PCRLean
