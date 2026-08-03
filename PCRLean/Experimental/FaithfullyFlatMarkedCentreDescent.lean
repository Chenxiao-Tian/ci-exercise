import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PCRLean.MarkedIdeal
import PCRLean.Experimental.FrobeniusNormalLocalCoordinateModel
import PCRLean.Experimental.PolynomialGraphArbitraryMarkCertificate

/-!
# Faithfully flat descent of marked graph centres

Faithful flatness reflects ideal containment because extension of ideals is
injective.  Consequently marked permissibility can be checked after a
faithfully flat base change; it is not merely an fpqc-local heuristic.

The main application packages a base ideal whose extension is a polynomial
graph centre.  From exact extension identities for the centre and source packet
we descend:

* uniqueness of the base centre;
* properness and non-whole-centre strictness;
* finite generation over a Noetherian base;
* Frobenius-normality of the centre filtration; and
* marked permissibility for every positive mark below the Frobenius block.

Regularity of the quotient, passive Tor safety, boundary SNC, and descent of the
actual blowup charts remain separate geometric obligations.
-/

namespace PCRLean
namespace Experimental
namespace FaithfullyFlatMarkedCentreDescent

noncomputable section

universe u v w x

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B]

/-- Extension of ideals along a faithfully flat algebra reflects containment. -/
theorem le_of_map_le_map
    {I J : Ideal A}
    (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) :
    I ≤ J := by
  intro a ha
  rw [← J.comap_map_eq_self_of_faithfullyFlat (B := B)]
  exact h (Ideal.mem_map_of_mem (algebraMap A B) ha)

/-- Extension of ideals along a faithfully flat algebra is injective. -/
theorem eq_of_map_eq_map
    {I J : Ideal A}
    (h : I.map (algebraMap A B) = J.map (algebraMap A B)) :
    I = J := by
  apply le_antisymm
  · exact le_of_map_le_map (B := B) h.le
  · exact le_of_map_le_map (B := B) h.ge

/-- The marked packet obtained by extending its ideal to the faithfully flat
algebra. -/
def mapPacket (P : MarkedIdeal.Packet A) : MarkedIdeal.Packet B where
  ideal := P.ideal.map (algebraMap A B)
  mark := P.mark
  mark_pos := P.mark_pos

/-- Marked permissibility descends from a faithfully flat extension. -/
theorem permissible_of_map
    (P : MarkedIdeal.Packet A) (C : Ideal A)
    (h : MarkedIdeal.Permissible (mapPacket (B := B) P)
      (C.map (algebraMap A B))) :
    MarkedIdeal.Permissible P C := by
  apply le_of_map_le_map (B := B)
  simpa [mapPacket, MarkedIdeal.Permissible, Ideal.map_pow] using h

/-- If the extended centre is proper, then the base centre is proper. -/
theorem ne_top_of_map_ne_top
    (I : Ideal A)
    (h : I.map (algebraMap A B) ≠ ⊤) : I ≠ ⊤ := by
  intro htop
  apply h
  simp [htop]

/-- If the extended centre is nonzero, then the base centre is nonzero. -/
theorem ne_bot_of_map_ne_bot
    (I : Ideal A)
    (h : I.map (algebraMap A B) ≠ ⊥) : I ≠ ⊥ := by
  intro hbot
  apply h
  simp [hbot]

section GraphModel

variable {R : Type w} [CommRing R] [IsDomain R]
variable {ι : Type x} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev GP := MvPolynomial ι R

variable [Algebra A (GP (R := R) (ι := ι))]
variable [Module.FaithfullyFlat A (GP (R := R) (ι := ι))]

open PolynomialGraphCentreHeredity
open PolynomialGraphBlowupHeredity
open PolynomialGraphFrobeniusCentreCertificate
open PolynomialGraphArbitraryMarkCertificate

/-- Exact faithfully flat graph model for a base centre and source packet. -/
structure GraphModel
    (C S : Ideal A) (h : ι → R) (q : Nat) where
  centre_extension :
    C.map (algebraMap A (GP (R := R) (ι := ι))) = graphIdeal h
  source_extension :
    S.map (algebraMap A (GP (R := R) (ι := ι))) = sourceIdeal h q

/-- Two base ideals with the same faithfully flat graph model are equal. -/
theorem centre_unique
    {C D : Ideal A} (h : ι → R)
    (hC : C.map (algebraMap A (GP (R := R) (ι := ι))) = graphIdeal h)
    (hD : D.map (algebraMap A (GP (R := R) (ι := ι))) = graphIdeal h) :
    C = D := by
  apply eq_of_map_eq_map (B := GP (R := R) (ι := ι))
  exact hC.trans hD.symm

variable [IsNoetherianRing A]
variable [IsNoetherianRing R] [IsRegularRing R]
variable (p : Nat) [Fact p.Prime] [CharP R p]

/-- Descended active-centre certificate supplied by one faithfully flat graph
model. -/
structure DescendedCertificate
    (C S : Ideal A) (h : ι → R) (e mark : Nat) where
  mark_pos : 0 < mark
  mark_le_block : mark ≤ p ^ e
  centre_proper : C ≠ ⊤
  centre_nonwhole : C ≠ ⊥
  centre_finiteType : C.FG
  centre_frobeniusNormal :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p C
  source_permissible :
    MarkedIdeal.Permissible
      (R := A) ⟨S, mark, mark_pos⟩ C

/-- Assemble the descended active-centre certificate. -/
noncomputable def descendGraphModel
    (C S : Ideal A) (h : ι → R) (e mark : Nat)
    (hmark_pos : 0 < mark)
    (hmark_le : mark ≤ p ^ e)
    (M : GraphModel C S h (p ^ e)) :
    DescendedCertificate p C S h e mark where
  mark_pos := hmark_pos
  mark_le_block := hmark_le
  centre_proper := ne_top_of_map_ne_top
    (B := GP (R := R) (ι := ι)) C (by
      rw [M.centre_extension]
      exact graphIdeal_ne_top h)
  centre_nonwhole := ne_bot_of_map_ne_bot
    (B := GP (R := R) (ι := ι)) C (by
      rw [M.centre_extension]
      exact graphIdeal_ne_bot h)
  centre_finiteType := IsNoetherian.noetherian C
  centre_frobeniusNormal :=
    FrobeniusNormalLocalCoordinateModel.reflects_of_graphModel
      (A := A) (R := R) (ι := ι) p C h M.centre_extension
  source_permissible := by
    apply permissible_of_map
      (B := GP (R := R) (ι := ι))
      (P := ⟨S, mark, hmark_pos⟩) (C := C)
    change S.map (algebraMap A (GP (R := R) (ι := ι))) ≤
      (C.map (algebraMap A (GP (R := R) (ι := ι)))) ^ mark
    rw [M.source_extension, M.centre_extension]
    exact (sourceIdeal_le_graphIdeal_pow h (p ^ e)).trans
      (PolynomialGraphArbitraryMarkCertificate.pow_le_pow_of_le
        (graphIdeal h) hmark_le)

end GraphModel

end

end FaithfullyFlatMarkedCentreDescent
end Experimental
end PCRLean
