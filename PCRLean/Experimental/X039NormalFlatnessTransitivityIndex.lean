import PCRLean.Experimental.HironakaTensorFlatnessCompiler
import PCRLean.Experimental.ExceptionalNoRecharge
import PCRLean.Experimental.NestedCarrierLegalizationRank

/-!
# MLEL-X039 / NTR-RFL integrated experimental index

X039 compresses the passive branch after X038.

```text
carrier flatness
-> purification-grading exceptional torsion vanishes
-> Hironaka tensor decomposition down a regular flag
-> normal flatness is transitive
-> no passive or exceptional-torsion recharge.
```

The remaining geometric compiler chooses one centre-enriched flatifier of a
raw carrier, factors it through a lower-dimensional regular word, recursively
legalizes every trace subcentre, and proves the all-chart Regular-Flag
Flat-Lift theorem.

The exact Lean leaves in this slice prove only:

* flatness transport across an abstract Hironaka tensor equivalence;
* simultaneous transport for a finite owner portfolio;
* absence and no recharge of certified exceptional-monomial torsion on a flat
  module; and
* well-founded arithmetic for carrier dimension, word height, Rees defect,
  contact, and debt.

They do not construct Hironaka's scheme map, a flatifier, a regular flag, an
ambient blowup word, the twisted Rees comparison, all-chart reentry,
termination, globalization, or general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X039NormalFlatnessTransitivityIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X039NormalFlatnessTransitivityIndex
end Experimental
end PCRLean
