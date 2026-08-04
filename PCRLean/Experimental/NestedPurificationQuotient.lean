import Mathlib

/-!
# Nested purification quotients

Let `H ≤ U ≤ M`.  The canonical map

```text
M/H -> M/U
```

is surjective and its kernel is exactly the image of `U` in `M/H`.  In the
X038 application,

```text
H = gr_L^ind(H^0_(u)(N)),
U = H^0_(u)(gr_L(N)).
```

Thus the purification--grading comparison has one canonical kernel, not an
untyped kernel/cokernel pair.  This file proves only the abstract quotient
compiler.  It does not construct the geometric graded modules or prove that
`U` is the full exceptional torsion layer.
-/

namespace PCRLean
namespace Experimental
namespace NestedPurificationQuotient

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {H U : Submodule R M}

/-- The canonical quotient map attached to nested submodules. -/
def quotientMap (hHU : H ≤ U) : M ⧸ H →ₗ[R] M ⧸ U :=
  Submodule.factor hHU

/-- The image of the larger layer inside the quotient by the inherited layer. -/
def defect (hHU : H ≤ U) : Submodule R (M ⧸ H) :=
  U.map H.mkQ

/-- The nested quotient map is surjective. -/
theorem quotientMap_surjective (hHU : H ≤ U) :
    Function.Surjective (quotientMap hHU) :=
  Submodule.factor_surjective hHU

/-- Its kernel is exactly the purification--grading defect. -/
theorem quotientMap_ker (hHU : H ≤ U) :
    LinearMap.ker (quotientMap hHU) = defect hHU := by
  simp [quotientMap, defect, Submodule.factor, Submodule.ker_mapQ]

/-- The defect vanishes exactly when the inherited and purified layers agree. -/
theorem defect_eq_bot_iff (hHU : H ≤ U) :
    defect hHU = ⊥ ↔ H = U := by
  constructor
  · intro hDef
    apply le_antisymm hHU
    intro x hxU
    have hxDef : H.mkQ x ∈ defect hHU := by
      exact ⟨x, hxU, rfl⟩
    rw [hDef] at hxDef
    have hzero : H.mkQ x = 0 := by
      simpa using hxDef
    exact (Submodule.Quotient.mk_eq_zero H).mp hzero
  · rintro rfl
    simp [defect]

/-- Vanishing of the defect upgrades the canonical epimorphism to an exact
linear equivalence. -/
noncomputable def interchangeEquiv
    (hHU : H ≤ U) (hDef : defect hHU = ⊥) :
    M ⧸ H ≃ₗ[R] M ⧸ U :=
  LinearEquiv.ofBijective (quotientMap hHU)
    ⟨LinearMap.ker_eq_bot.mp (by simpa [quotientMap_ker hHU] using hDef),
      quotientMap_surjective hHU⟩

/-- The equivalence is the canonical nested quotient map. -/
theorem interchangeEquiv_apply
    (hHU : H ≤ U) (hDef : defect hHU = ⊥) (x : M ⧸ H) :
    interchangeEquiv hHU hDef x = quotientMap hHU x := by
  rfl

end

end NestedPurificationQuotient
end Experimental
end PCRLean
