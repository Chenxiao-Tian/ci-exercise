import Mathlib
import PCRLean.MarkedIdeal

/-!
# Experimental marked-power synthesis for hybrid centres

A Frobenius-root component and an ordinary/Hasse-defect component can each
control different terms of one marked equation.  If a root term lies in the
`m`th power of one component ideal and a defect term lies in the `m`th power of
a second component ideal, then their sum or difference lies in the `m`th power
of the joined centre.

This is the general algebraic mechanism behind the hybrid cusp centre
`(x,y)` for `y^p-x^(p+1)`.  It proves marked permissibility only.  Regularity,
strictness, singular-locus containment, owner safety, and hereditary transport
remain independent gates.
-/

namespace PCRLean
namespace Experimental
namespace HybridMarkedSynthesis

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The power of the left component is contained in the power of the hybrid
join. -/
theorem pow_le_hybrid_left
    (A B : Ideal R) (m : Nat) :
    A ^ m ≤ (A ⊔ B) ^ m := by
  gcongr
  exact le_sup_left

/-- The power of the right component is contained in the power of the hybrid
join. -/
theorem pow_le_hybrid_right
    (A B : Ideal R) (m : Nat) :
    B ^ m ≤ (A ⊔ B) ^ m := by
  gcongr
  exact le_sup_right

/-- Two terms controlled by different component ideals add inside the marked
power of the hybrid centre. -/
theorem add_mem_hybrid_pow
    {A B : Ideal R} {f g : R} {m : Nat}
    (hf : f ∈ A ^ m) (hg : g ∈ B ^ m) :
    f + g ∈ (A ⊔ B) ^ m := by
  exact ((A ⊔ B) ^ m).add_mem
    (pow_le_hybrid_left A B m hf)
    (pow_le_hybrid_right A B m hg)

/-- Difference form used by inseparable cusp equations. -/
theorem sub_mem_hybrid_pow
    {A B : Ideal R} {f g : R} {m : Nat}
    (hf : f ∈ A ^ m) (hg : g ∈ B ^ m) :
    f - g ∈ (A ⊔ B) ^ m := by
  exact ((A ⊔ B) ^ m).sub_mem
    (pow_le_hybrid_left A B m hf)
    (pow_le_hybrid_right A B m hg)

/-- If a principal marked equation decomposes into root and defect terms
controlled at the same mark, their joined centre is permissible. -/
theorem principalPacket_permissible_of_add_components
    {A B : Ideal R} {f g : R} {m : Nat}
    (hm : 0 < m)
    (hf : f ∈ A ^ m) (hg : g ∈ B ^ m) :
    MarkedIdeal.Permissible
      (R := R) ⟨Ideal.span {f + g}, m, hm⟩ (A ⊔ B) := by
  exact MarkedIdeal.permissible_span_singleton hm
    (add_mem_hybrid_pow hf hg)

/-- Difference version of the principal marked synthesis theorem. -/
theorem principalPacket_permissible_of_sub_components
    {A B : Ideal R} {f g : R} {m : Nat}
    (hm : 0 < m)
    (hf : f ∈ A ^ m) (hg : g ∈ B ^ m) :
    MarkedIdeal.Permissible
      (R := R) ⟨Ideal.span {f - g}, m, hm⟩ (A ⊔ B) := by
  exact MarkedIdeal.permissible_span_singleton hm
    (sub_mem_hybrid_pow hf hg)

/-- The same synthesis works at the level of two marked ideals: if each owner
ideal is already controlled by its own component, their union is controlled by
the hybrid join. -/
theorem sup_packet_le_hybrid_pow
    {I J A B : Ideal R} {m : Nat}
    (hI : I ≤ A ^ m) (hJ : J ≤ B ^ m) :
    I ⊔ J ≤ (A ⊔ B) ^ m := by
  apply sup_le
  · exact hI.trans (pow_le_hybrid_left A B m)
  · exact hJ.trans (pow_le_hybrid_right A B m)

end

end HybridMarkedSynthesis
end Experimental
end PCRLean
