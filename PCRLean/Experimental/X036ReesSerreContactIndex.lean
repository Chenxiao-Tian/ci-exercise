import PCRLean.Experimental.FinitePrefixTailCriterion
import PCRLean.Experimental.FiniteGateProductPrime
import PCRLean.Experimental.ContactCancellationRank

/-!
# MLEL-X036 / RSC-CCD integrated experimental index

The X035 regular-support branch is refined into two finite stages.

```text
passive normal flatness
-> finite low-degree window + projective Rees--Serre tail

regular-support nilpotent intersection
-> owner-resolved contact-cancellation ideal
-> projective directional-depth flag
-> reduced-support blowup
-> tangent-rank drop or one-unit contact-depth shift.
```

The exact Lean leaves in this slice prove only:

* finite-prefix/eventual-tail coverage;
* finite-product prime avoidance for joint-defect ideals; and
* the well-founded tangent-rank/contact-depth arithmetic.

They do not prove relative Serre vanishing, flattening stratification, the
scheme-level finite normal-flatness criterion, graph normal forms, construction
or base change of the contact-cancellation ideal, the all-chart blowup shift,
passive or logarithmic legality, hereditary no-reset, termination, or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X036ReesSerreContactIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X036ReesSerreContactIndex
end Experimental
end PCRLean
