import Mathlib

/-!
# Controlled-core transform factorization

The first X038 candidate used two surjections to one common core.  The second
surjection is false before the weak/controlled transform filtration is
saturated: for example `J = (q*y)` and `L = Sat_q(J) = (y)` give a map
`J/J^2 -> L/L^2` whose image is only the `q`-multiple of the target.

The corrected primitive is a factorization

```text
old controlled graded object -->> controlled core --> new normal graded object.
```

The first map is surjective; its kernel is the Tor/base-change defect.  The
second map can have both kernel and cokernel; these are the two
Valabrega/saturation defects.  If all three defects vanish, the old and new
objects are canonically equivalent.

This file proves only the abstract linear-algebra compiler.  It does not
construct the geometric maps or identify their defects.
-/

namespace PCRLean
namespace Experimental
namespace ControlledCoreInterchange

noncomputable section

universe u v w z

variable {R : Type u} [CommRing R]
variable (Old : Type v) (Core : Type w) (New : Type z)
variable [AddCommGroup Old] [Module R Old]
variable [AddCommGroup Core] [Module R Core]
variable [AddCommGroup New] [Module R New]

/-- Canonical two-stage comparison through the controlled-transform core. -/
structure Factorization where
  oldToCore : Old →ₗ[R] Core
  coreToNew : Core →ₗ[R] New
  old_surjective : Function.Surjective oldToCore

namespace Factorization

variable {Old Core New}

/-- The Tor/base-change defect. -/
abbrev torDefect
    (f : Factorization (R := R) Old Core New) : Submodule R Old :=
  LinearMap.ker f.oldToCore

/-- The Valabrega intersection defect. -/
abbrev valabregaKernel
    (f : Factorization (R := R) Old Core New) : Submodule R Core :=
  LinearMap.ker f.coreToNew

/-- The image of the controlled core in the new normal graded object. -/
abbrev controlledRange
    (f : Factorization (R := R) Old Core New) : Submodule R New :=
  LinearMap.range f.coreToNew

/-- Vanishing Tor defect makes the old-to-core epimorphism an equivalence. -/
noncomputable def oldEquiv
    (f : Factorization (R := R) Old Core New)
    (hTor : f.torDefect = ⊥) :
    Old ≃ₗ[R] Core :=
  LinearEquiv.ofBijective f.oldToCore
    ⟨LinearMap.ker_eq_bot.mp hTor, f.old_surjective⟩

/-- Vanishing Valabrega kernel and cokernel makes the controlled-core map an
equivalence.  `hCoker` is expressed as full range. -/
noncomputable def coreEquiv
    (f : Factorization (R := R) Old Core New)
    (hKer : f.valabregaKernel = ⊥)
    (hCoker : f.controlledRange = ⊤) :
    Core ≃ₗ[R] New :=
  LinearEquiv.ofBijective f.coreToNew
    ⟨LinearMap.ker_eq_bot.mp hKer, LinearMap.range_eq_top.mp hCoker⟩

/-- Exact transform interchange after all Tor--Valabrega defects vanish. -/
noncomputable def interchangeEquiv
    (f : Factorization (R := R) Old Core New)
    (hTor : f.torDefect = ⊥)
    (hKer : f.valabregaKernel = ⊥)
    (hCoker : f.controlledRange = ⊤) :
    Old ≃ₗ[R] New :=
  (f.oldEquiv hTor).trans (f.coreEquiv hKer hCoker)

/-- The final equivalence is compatible with the two-stage comparison. -/
theorem interchangeEquiv_apply
    (f : Factorization (R := R) Old Core New)
    (hTor : f.torDefect = ⊥)
    (hKer : f.valabregaKernel = ⊥)
    (hCoker : f.controlledRange = ⊤)
    (x : Old) :
    f.interchangeEquiv hTor hKer hCoker x =
      f.coreToNew (f.oldToCore x) := by
  rfl

/-- Existential compiler form for higher-level certificates. -/
theorem nonempty_equiv_of_defects_vanish
    (f : Factorization (R := R) Old Core New)
    (hTor : f.torDefect = ⊥)
    (hKer : f.valabregaKernel = ⊥)
    (hCoker : f.controlledRange = ⊤) :
    Nonempty (Old ≃ₗ[R] New) :=
  ⟨f.interchangeEquiv hTor hKer hCoker⟩

end Factorization

end

end ControlledCoreInterchange
end Experimental
end PCRLean
