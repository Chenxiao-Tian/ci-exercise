import PCRLean.Experimental.ExceptionalTorsionLayers
import PCRLean.Experimental.NestedPurificationQuotient
import PCRLean.Experimental.ArtinReesTailCompiler
import PCRLean.Experimental.FlatExceptionalTorsionKill
import PCRLean.Experimental.ExceptionalInterchangeRank

/-!
# MLEL-X038 / PGI-ERD integrated experimental index

The X038 candidate theorem replaces the arbitrary kernel/cokernel Rees
interchange defect by a structured two-stage exceptional packet.

On one chart, for a finite ambient pullback module `N`, transformed carrier
ideal `L`, exceptional parameter `u`, and `T = H^0_(u)(N)`, put

```text
A = gr_L(N),
H = gr_L^ind(T),
U = H^0_(u)(A).
```

The proposed exact sequence is

```text
0 -> U/H
  -> gr_L(N/T)
  -> A/U
  -> 0.
```

The abstract nested-submodule quotient map and its exact kernel are explicit
Lean leaves.  Geometry must still identify `gr_L(N/T)` with `A/H`, prove
`H <= U`, and prove that `U/H` is all exceptional-power torsion of that quotient.
Once the purified associated graded is flat over a carrier on which the
exceptional equation is a nonzerodivisor, the new flat-torsion endpoint proves
that this defect is zero.  Artin--Rees supplies a finite transition window once
the induced filtration is constructed.  A separate Rees base-change/twist
comparison remains necessary; its coherent kernel and cokernel are supported
on the same exceptional divisor.

The Lean leaves in this slice prove only nested-layer clean/defect coverage,
the abstract nested quotient kernel, finite prefix/tail induction, flatness
implies absence of exceptional power torsion, and the well-founded arithmetic
of the proposed rank.  They do not prove the geometric exact sequence,
Artin--Rees finiteness, construction of the flatifier, base change, all-chart
Rees comparison, ambient realization, no-reset, termination, or general
positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X038PurificationGradingInterchangeIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X038PurificationGradingInterchangeIndex
end Experimental
end PCRLean
