import Mathlib

/-!
# Finite spanning sets give finite-free surjections

A finite spanning set of a module determines a canonical linear-combination
map from a finite free module, and that map is surjective. This is the finite
generation half of the X032 split-presentation bridge.
-/

namespace PCRLean
namespace Experimental
namespace FiniteSpanningSetSurjectionAtomic

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Linear-combination map attached to a finite spanning family. -/
def generatorMap (s : Finset P) : (s → R) →ₗ[R] P where
  toFun a := ∑ i : s, (a i) • (i : P)
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp [mul_smul, Finset.smul_sum]

/-- Each chosen generator lies in the range of the generator map. -/
theorem generator_mem_range (s : Finset P) (i : s) :
    (i : P) ∈ LinearMap.range (generatorMap (R := R) s) := by
  classical
  refine ⟨Pi.single i 1, ?_⟩
  simp [generatorMap]

/-- The span of the chosen family is contained in the range. -/
theorem span_le_range (s : Finset P) :
    Submodule.span R (s : Set P) ≤
      LinearMap.range (generatorMap (R := R) s) := by
  apply Submodule.span_le.mpr
  intro x hx
  exact generator_mem_range (R := R) s ⟨x, hx⟩

/-- If the finite family spans, the generator map is surjective. -/
theorem generatorMap_surjective
    (s : Finset P) (hspan : Submodule.span R (s : Set P) = ⊤) :
    Function.Surjective (generatorMap (R := R) s) := by
  intro x
  have hx : x ∈ Submodule.span R (s : Set P) := by
    rw [hspan]
    exact Submodule.mem_top
  exact span_le_range (R := R) s hx

end

end FiniteSpanningSetSurjectionAtomic
end Experimental
end PCRLean
