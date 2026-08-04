import PCRLean.Experimental.FiniteGradedFlatnessCompiler
import PCRLean.Experimental.FinitePassivePortfolio
import PCRLean.Experimental.AnchorContactCleaning
import PCRLean.Experimental.LegalizationPhaseRank

/-!
# MLEL-X036 / PNF-ACL integrated experimental index

The X036 candidate architecture replaces two undifferentiated X035 gates by
lower-dimensional preparatory macros.

```text
candidate regular centre C
-> projectivized normal passive packet
-> finite low-degree / projective-tail decomposition
-> flatification on C
-> ambient lift of a regular word dominating the flatifier
-> passive-normal-flat strict transform C'

regular-support bad intersection
-> finite anchor family
-> contact ideals on the regular anchors
-> lower-dimensional principalization
-> ambient contact cleaning
-> empty or clean transformed intersection.
```

The exact Lean leaves in this slice prove only:

* finite-tail compilation of flat graded pieces;
* simultaneous compilation for a finite passive portfolio;
* the scalar exceptional-contact factorization and strict contact drop; and
* the well-founded contact/passive/debt rank arithmetic.

They do not prove Rees--Serre comparison, Raynaud--Gruson flatification,
projective-normal transport, anchor-contact transform compatibility, ambient
lifting, log-SNC legalization, all-chart reentry, termination, or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X036ProjectiveNormalLegalizationIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X036ProjectiveNormalLegalizationIndex
end Experimental
end PCRLean
