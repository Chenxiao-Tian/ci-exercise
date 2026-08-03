import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.Experimental.MarkedPermissibilityFaithfullyFlatDescent
import PCRLean.Experimental.FrobeniusNormalLocalCoordinateModel
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate

/-!
# Faithfully flat compiler for polynomial graph centre models

Suppose an actual centre ideal `C ⊂ A` and source ideal `S ⊂ A` become, after a
faithfully flat extension to a polynomial graph chart `R[Z_i]`, exactly

`C B = (Z_i - h_i)` and `S B = ((Z_i - h_i)^q)`.

For every positive mark `m ≤ q`, the graph-chart calculation descends to the
base ring and proves:

* `C` is neither `⊤` nor `⊥`;
* `S ≤ C^m`, hence the marked source is permissible; and
* the `C`-adic filtration reflects all prime-power Frobenius roots.

The local graph chart also carries an exact regular quotient and all-chart
terminal/pure-debt certificate, but this module deliberately does not claim
that regularity of the quotient or the actual blowup atlas has descended.
Those are separate fpqc/scheme-level effectivity obligations.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatGraphCentreCompiler

noncomputable section

universe u v w x

variable {A : Type u} {R : Type v}
variable [CommRing A] [CommRing R] [IsDomain R]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev B := MvPolynomial ι R

variable [Algebra A (B (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (B (R := R) (ι := ι))]

open MarkedPermissibilityFaithfullyFlatDescent
open FrobeniusNormalFaithfullyFlatDescent
open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphArbitraryMarkCertificate

/-- A faithfully flat presentation of a base centre and source by one
polynomial graph packet. -/
structure Model
    (centre source : Ideal A) (h : ι → R) (q : Nat) where
  centre_eq : extend (B := B (R := R) (ι := ι)) centre = graphIdeal h
  source_eq : extend (B := B (R := R) (ι := ι)) source = sourceIdeal h q

namespace Model

variable {centre source : Ideal A} {h : ι → R} {q : Nat}
    (M : Model (A := A) (R := R) centre source h q)

/-- The base centre is not the empty closed subscheme. -/
theorem centre_ne_top : centre ≠ ⊤ := by
  intro htop
  have hmap :
      extend (B := B (R := R) (ι := ι)) centre = ⊤ :=
    (extend_eq_top_iff
      (B := B (R := R) (ι := ι)) centre).2 htop
  rw [M.centre_eq] at hmap
  exact graphIdeal_ne_top h hmap

/-- The base centre is not the whole ambient space. -/
theorem centre_ne_bot : centre ≠ ⊥ := by
  intro hbot
  have hmap :
      extend (B := B (R := R) (ι := ι)) centre = ⊥ :=
    (extend_eq_bot_iff
      (B := B (R := R) (ι := ι)) centre).2 hbot
  rw [M.centre_eq] at hmap
  exact PolynomialGraphFrobeniusCentreCertificate.graphIdeal_ne_bot h hmap

/-- Local graph containment at an arbitrary positive submark. -/
theorem extended_source_le_extended_centre_pow
    {mark : Nat} (hmark : mark ≤ q) :
    extend (B := B (R := R) (ι := ι)) source ≤
      (extend (B := B (R := R) (ι := ι)) centre) ^ mark := by
  rw [M.source_eq, M.centre_eq]
  apply (sourceIdeal_le_graphIdeal_pow h q).trans
  exact PolynomialGraphArbitraryMarkCertificate.pow_le_pow_of_le
    (graphIdeal h) hmark

/-- Marked permissibility descends from the graph chart. -/
theorem source_le_centre_pow
    {mark : Nat} (hmark : mark ≤ q) :
    source ≤ centre ^ mark := by
  exact le_pow_of_extend_le_pow
    (B := B (R := R) (ι := ι))
    (M.extended_source_le_extended_centre_pow hmark)

/-- Packet-level marked permissibility in the base ring. -/
theorem source_permissible
    {mark : Nat} (hmark_pos : 0 < mark) (hmark : mark ≤ q) :
    MarkedIdeal.Permissible
      (R := A) ⟨source, mark, hmark_pos⟩ centre :=
  M.source_le_centre_pow hmark

variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Frobenius-normality descends from the graph model. -/
theorem centre_reflectsFrobeniusPowers :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p centre := by
  exact FrobeniusNormalLocalCoordinateModel.reflects_of_graphModel
    (A := A) (R := R) (ι := ι) p centre h M.centre_eq

end Model

/-- Combined base-ring certificate produced by a faithfully flat graph model. -/
structure Certificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (centre source : Ideal A) (h : ι → R)
    (q mark : Nat) where
  mark_pos : 0 < mark
  mark_le_block : mark ≤ q
  model : Model (A := A) (R := R) centre source h q
  centre_ne_top : centre ≠ ⊤
  centre_ne_bot : centre ≠ ⊥
  sourcePermissible :
    MarkedIdeal.Permissible (R := A)
      ⟨source, mark, mark_pos⟩ centre
  frobeniusNormal :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p centre

/-- Assemble the base-ring certificate from the local graph model. -/
noncomputable def certificate
    (p : Nat) [Fact p.Prime] [CharP R p]
    (centre source : Ideal A) (h : ι → R)
    (q mark : Nat) (hmark_pos : 0 < mark) (hmark : mark ≤ q)
    (M : Model (A := A) (R := R) centre source h q) :
    Certificate (A := A) (R := R) p centre source h q mark where
  mark_pos := hmark_pos
  mark_le_block := hmark
  model := M
  centre_ne_top := M.centre_ne_top
  centre_ne_bot := M.centre_ne_bot
  sourcePermissible := M.source_permissible hmark_pos hmark
  frobeniusNormal := M.centre_reflectsFrobeniusPowers p

end

end FaithfullyFlatGraphCentreCompiler
end Experimental
end PCRLean
