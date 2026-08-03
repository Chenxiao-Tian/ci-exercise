import Mathlib
import PCRLean.Experimental.DualPacketRegularCentre

/-!
# Experimental boundary--centre conormal transversality

A boundary conormal packet and a centre conormal packet are first-order SNC
compatible when their spans meet only in zero.  If each packet is internally
linearly independent, every mixed linear relation has all coefficients zero.
Thus their union is a genuine combined conormal frame, without choosing
coordinates or relying only on disjoint index tags.

This is the linear algebraic boundary gate.  It does not lift the combined
frame to regular parameters in a nonlinear local ring or prove that the
condition is preserved by every blowup chart.
-/

namespace PCRLean
namespace Experimental
namespace DualPacketBoundaryTransversality

noncomputable section

universe u v w x

variable {K : Type u} [Field K]
variable {T : Type v} [AddCommGroup T] [Module K T]
variable {β : Type w} {κ : Type x}
variable [Fintype β] [Fintype κ]

abbrev Cotangent := Module.Dual K T

/-- One boundary packet and one centre packet with internal independence and
disjoint cotangent spans. -/
structure Certificate
    (boundary : β → Cotangent (K := K) (T := T))
    (centre : κ → Cotangent (K := K) (T := T)) where
  boundary_independent : LinearIndependent K boundary
  centre_independent : LinearIndependent K centre
  spans_disjoint : Disjoint
    (Submodule.span K (Set.range boundary))
    (Submodule.span K (Set.range centre))

namespace Certificate

variable
    {boundary : β → Cotangent (K := K) (T := T)}
    {centre : κ → Cotangent (K := K) (T := T)}
    (C : Certificate boundary centre)

/-- Any vector in both conormal spans is zero. -/
theorem eq_zero_of_mem_both
    {f : Cotangent (K := K) (T := T)}
    (hb : f ∈ Submodule.span K (Set.range boundary))
    (hc : f ∈ Submodule.span K (Set.range centre)) : f = 0 := by
  exact (disjoint_left.mp C.spans_disjoint) hb hc

/-- Every mixed boundary--centre linear relation has all coefficients zero. -/
theorem mixed_relation_coefficients_zero
    (a : β → K) (c : κ → K)
    (hrel :
      (∑ b : β, a b • boundary b) +
        (∑ i : κ, c i • centre i) = 0) :
    (∀ b, a b = 0) ∧ ∀ i, c i = 0 := by
  let fb : Cotangent (K := K) (T := T) :=
    ∑ b : β, a b • boundary b
  let fc : Cotangent (K := K) (T := T) :=
    ∑ i : κ, c i • centre i
  have hfbSpan : fb ∈ Submodule.span K (Set.range boundary) := by
    apply Submodule.sum_mem
    intro b hb
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b, rfl⟩)
  have hfcSpan : fc ∈ Submodule.span K (Set.range centre) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hfb_eq_neg_fc : fb = -fc := by
    dsimp [fb, fc]
    abel
  have hfbCentre : fb ∈ Submodule.span K (Set.range centre) := by
    rw [hfb_eq_neg_fc]
    exact (Submodule.span K (Set.range centre)).neg_mem hfcSpan
  have hfbZero : fb = 0 := C.eq_zero_of_mem_both hfbSpan hfbCentre
  have hfcZero : fc = 0 := by
    dsimp [fb, fc] at hrel hfbZero ⊢
    rw [hfbZero] at hrel
    simpa using hrel
  constructor
  · exact (Fintype.linearIndependent_iff.mp C.boundary_independent) a hfbZero
  · exact (Fintype.linearIndependent_iff.mp C.centre_independent) c hfcZero

/-- The two spans form an internal direct sum. -/
theorem isCompl_of_sup_eq_top
    (hsup :
      Submodule.span K (Set.range boundary) ⊔
        Submodule.span K (Set.range centre) = ⊤) :
    IsCompl
      (Submodule.span K (Set.range boundary))
      (Submodule.span K (Set.range centre)) :=
  ⟨C.spans_disjoint, codisjoint_iff.mpr hsup⟩

end Certificate

end

end DualPacketBoundaryTransversality
end Experimental
end PCRLean
