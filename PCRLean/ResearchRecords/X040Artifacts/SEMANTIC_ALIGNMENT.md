# X040 Semantic Alignment

## Scope rule

The X040 Lean declarations certify only finite-set arrangement combinatorics,
elementary ideal-product containments, a crossing-source countermodel, and
well-founded rank arithmetic.  They do not certify any Rees-Serre comparison,
functorial flatification, scheme-level blowup, common refinement,
principalization, strict transform, wonderful model, hereditary reentry,
termination, or resolution theorem.

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Certified content | Not certified |
|---|---|---|---|
| Minimal-stratum nesting | `MinimalStratumNesting.disjoint_or_subset` | Finite intersection-closed set family: a minimal nonempty member is disjoint from or contained in every member | Scheme intersections, regularity, transformed arrangements, wonderful blowups |
| Binary common trace product | `CommonTraceProduct.product_le_inf` | The product of two ideals is contained in both factors | Blowup factorization, finite products, source labels, support dimension |
| Source-product symmetry | `CommonTraceProduct.swap_sources` | Binary ideal multiplication is commutative | Equivariance of the complete geometric algorithm or flatifier source |
| Finite completion universe | `FiniteArrangementCompletion.inter_mem_completion` | One finite powerset over-approximation contains all finite-set intersections | Effectivity or regularity of scheme-theoretic strata |
| Crossing-source no-go | `CrossCarrierCompletionModel.not_disjoint` and subset no-go lemmas | A finite model has overlapping nonnested sources and a deeper intersection | Existence of the analogous algebraic-geometric blowup word |
| Common budget rank | `CommonFlatifierBudgetRank.rank_wellFounded` | The proposed three-coordinate relation is well founded | Every actual macro lowers a coordinate |

## Standard inputs not formalized here

```text
functorial flatification of proper morphisms by admissible blowups;
finite composition of blowups is a blowup;
finite product blowup is a common refinement;
strict transform equals induced carrier blowup;
flat strict transform is pullback;
componentwise admissible source support has smaller dimension;
Hironaka normal-flatness transitivity;
wonderful building-set serialization.
```

Each still needs the exact scheme interface and source/owner/boundary semantics
used by this project.  In particular, a general functorial proper-flatification
theorem does not itself construct the finite projective Rees-Serre packet,
prove equivalence with affine all-degree normal flatness, or replace singular
flatifier centres by regular jointly legal ambient centres in positive
characteristic.

## Candidate correction boundary

The complete affine normal-cone module is sufficient to formulate all-degree
normal flatness and to obtain nonfunctorial flatifier existence.  It does not by
itself select one flatifier word compatible with smooth/étale base change.  The
proper Rees-Serre packet is restored solely as a canonicality/functoriality
engine and must retain the finite low/transition degrees; a projective tail
alone is insufficient.

## Forbidden extrapolations

The X040 source does not license any claim that:

```text
the finite functorial Rees-Serre packet has been constructed;
the proper flatifier sources already have regular centres;
the common product centre is regular;
the lower-dimensional relative principalization theorem is proved;
common-refinement strict transforms agree sourcewise;
all source intersections are regular;
Regular-Flag Flat-Lift is proved;
passive legality cannot recharge geometrically;
all-chart no-reset or termination is proved;
general positive-characteristic resolution is proved.
```

## Truth boundary

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```
