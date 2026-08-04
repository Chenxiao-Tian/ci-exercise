import PCRLean.Experimental.ExceptionalTorsionLayers
import PCRLean.Experimental.ArtinReesTailCompiler
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

Moreover `U/H` is the exceptional-power torsion of `gr_L(N/T)`.  Artin--Rees
should make `H` and hence the defect finite graded.  A separate Rees
base-change/twist comparison has coherent kernel and cokernel supported on the
same exceptional divisor.  Vanishing gives exact ambient/projective-normal
transport; nonvanishing is a lower-dimensional exceptional packet.

The Lean leaves in this slice prove only nested-layer clean/defect coverage,
finite prefix/tail induction, and the well-founded arithmetic of the proposed
rank.  They do not prove the exact sequence, Artin--Rees finiteness, base change,
all-chart Rees comparison, divisorial elimination, no-reset, termination, or
general positive-characteristic resolution.
-/

namespace PCRLean
namespace Experimental
namespace X038PurificationGradingInterchangeIndex

/-- Integrated-source elaboration marker. -/
theorem loaded : True := True.intro

end X038PurificationGradingInterchangeIndex
end Experimental
end PCRLean
