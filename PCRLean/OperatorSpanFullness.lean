import Mathlib
import PCRLean.IdealEndomorphismDescent

/-!
# Full invariance from a spanning operator packet

A finite Hasse--Cartier packet need not literally list every endomorphism.
It is enough that its linear span be the full endomorphism module.  Stability
under the packet then propagates, by linearity, to stability under every
endomorphism.  Combined with finite-free ideal descent, this turns an
operator-spanning certificate into an actual descended ideal.
-/

namespace PCRLean
namespace OperatorSpanFullness

noncomputable section

universe u v w

variable {R : Type u} {M : Type v} {κ : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A submodule is stable under the declared operator packet. -/
def Stable (ops : κ → Module.End R M) (N : Submodule R M) : Prop :=
  ∀ i x, x ∈ N → ops i x ∈ N

/-- The declared packet linearly spans the full endomorphism module. -/
def SpansEnd (ops : κ → Module.End R M) : Prop :=
  Submodule.span R (Set.range ops) = ⊤

/-- Stability under a spanning packet propagates to every endomorphism. -/
theorem fullyInvariant_of_spansEnd
    (ops : κ → Module.End R M) (N : Submodule R M)
    (hstable : Stable ops N) (hspan : SpansEnd ops) :
    FiniteFreeEndomorphismDescent.FullyInvariant N := by
  intro T x hx
  have hT : T ∈ Submodule.span R (Set.range ops) := by
    rw [hspan]
    trivial
  induction hT using Submodule.span_induction with
  | mem T hT =>
      rcases hT with ⟨i, rfl⟩
      exact hstable i x hx
  | zero =>
      simpa using N.zero_mem
  | add S T hS hT hSx hTx =>
      simpa using N.add_mem hSx hTx
  | smul r T hT hTx =>
      simpa using N.smul_mem r hTx

section Ideal

universe x y

variable {A : Type x} {ι : Type y}
variable [CommRing A] [Algebra R A]
variable [Fintype ι] [DecidableEq ι]

/-- A spanning family of base-linear operators preserving an ideal forces the
ideal to descend from the base ring. -/
theorem ideal_eq_map_comap_of_spanning_packet
    (F : IdealEndomorphismDescent.UnitFrame
      (R := R) (A := A) (ι := ι))
    (ops : κ → Module.End R A) (I : Ideal A)
    (hstable : Stable ops
      (IdealEndomorphismDescent.idealSubmodule (R := R) I))
    (hspan : SpansEnd ops) :
    I = (I.comap (algebraMap R A)).map (algebraMap R A) := by
  apply IdealEndomorphismDescent.UnitFrame.ideal_eq_map_comap_of_fullyInvariant
    F I
  exact fullyInvariant_of_spansEnd ops
    (IdealEndomorphismDescent.idealSubmodule (R := R) I) hstable hspan

end Ideal

end

end OperatorSpanFullness
end PCRLean
