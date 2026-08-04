import Mathlib

/-!
# Centre-enriched pure-transform data

A blowup morphism does not by itself determine the strict or pure transform of
a sheaf: the chosen centre controls which exceptional-supported sections are
removed.  In particular, an effective Cartier centre on a carrier may give the
identity carrier morphism while still carrying a nontrivial pure-transform
payload.

This file records the exact abstract information-loss statement needed by the
X037 candidate architecture.  A carrier step stores a vertical submodule to be
quotiented from the pulled-back module.  Forgetting that payload and retaining
only a trivial carrier-morphism token is not injective as soon as the module is
nontrivial.

The file proves no scheme-level blowup, strict-transform, normal-flatness, or
positive-characteristic resolution theorem.
-/

namespace PCRLean
namespace Experimental
namespace CentreEnrichedPureTransform

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Centre-enriched carrier data: `vertical` is the submodule removed in the
pure transform. -/
structure Step where
  vertical : Submodule R M

/-- The carrier morphism token deliberately forgets the centre/pure-transform
payload.  It models a carrier blowup that is the identity as a morphism. -/
def forgetCarrierMorphism (_ : Step (R := R) M) : Unit := ()

/-- The abstract pure-transform module attached to a centre-enriched step. -/
abbrev PureTransform (s : Step (R := R) M) := M ⧸ s.vertical

/-- On a nontrivial module, the carrier-morphism token cannot recover the
centre/pure-transform payload.  Thus a morphism-only domination statement is
insufficient for strict-transform transport. -/
theorem forgetCarrierMorphism_not_injective [Nontrivial M] :
    ¬ Function.Injective (forgetCarrierMorphism (R := R) M) := by
  intro h
  let s : Step (R := R) M := ⟨⊥⟩
  let t : Step (R := R) M := ⟨⊤⟩
  have hst : s = t := h rfl
  have hv : s.vertical = t.vertical := congrArg Step.vertical hst
  have hbotTop : (⊥ : Submodule R M) = ⊤ := by
    simpa [s, t] using hv
  exact (bot_ne_top : (⊥ : Submodule R M) ≠ ⊤) hbotTop

/-- Existential form of the same no-go, convenient for counterexample ledgers. -/
theorem exists_same_morphism_distinct_payload [Nontrivial M] :
    ∃ s t : Step (R := R) M,
      forgetCarrierMorphism (R := R) M s =
        forgetCarrierMorphism (R := R) M t ∧ s ≠ t := by
  let s : Step (R := R) M := ⟨⊥⟩
  let t : Step (R := R) M := ⟨⊤⟩
  refine ⟨s, t, rfl, ?_⟩
  intro hst
  have hv : s.vertical = t.vertical := congrArg Step.vertical hst
  have hbotTop : (⊥ : Submodule R M) = ⊤ := by
    simpa [s, t] using hv
  exact (bot_ne_top : (⊥ : Submodule R M) ≠ ⊤) hbotTop

end

end CentreEnrichedPureTransform
end Experimental
end PCRLean
