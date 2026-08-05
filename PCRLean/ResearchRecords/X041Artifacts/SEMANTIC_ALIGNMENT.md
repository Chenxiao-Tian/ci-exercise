# X041 Semantic Alignment

## Scope rule

The X041 Lean declarations certify only direct-sum flatness, transport across
linear equivalences, finite portfolio compilation, and well-founded rank
arithmetic.  They do not certify a symmetric algebra, projective bundle,
homogenized coherent sheaf, functorial flatifier, blowup, strict transform,
regular flag, overlap, hereditary successor, termination, or resolution
algorithm.

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Certified content | Not certified |
|---|---|---|---|
| Degree-`d` homogenized slice | `HomogenizedGradedFlatness.Slice` | The abstract finite direct sum of `Piece 0,...,Piece d` | Identification with the degree-`d` part of `G[z]` |
| Homogenized flatness | `HomogenizedGradedFlatness.homogenizedFlat_iff_pieceFlat` | Flatness of the triangular direct-sum module iff every family member is flat | Relative Proj, coherence, the `D_+(z)` chart, or geometric normal flatness |
| Degreewise flag transport | `DegreewiseFlagFlatLiftCompiler.Transport` | A family of supplied linear equivalences | Construction from a blowup chart or exceptional line twist |
| Flag-lift flatness | `DegreewiseFlagFlatLiftCompiler.Transport.newGradedFlat` | Supplied degreewise equivalences and old flatness imply flatness of the new direct sum | Tor safety, Rees exactness, chart coverage, or overlap equality |
| Common-refinement source certificate | `SourceWordCofinalityCompiler.Certificate` | Supplied source-by-source linear equivalences | Composite word ideals, product blowups, strict-transform transitivity, or flat pullback |
| Common source portfolio flatness | `SourceWordCofinalityCompiler.Certificate.portfolioFlat` | Flat terminal modules plus supplied equivalences imply flatness of the finite common portfolio | Any scheme-level common refinement |
| Carrier/source/flag rank | `HomogenizedCarrierRank.rank_wellFounded` | The abstract four-coordinate lexicographic relation is well founded | Every actual geometric macro lowers a coordinate |

## Standard mathematical inputs identified but not formalized here

```text
finite graded G gives finite total-degree G[z] over S[z];
D_+(z) in Proj(S[z]) recovers Spec(S) and G;
Rydh functorial flatification for proper coherent sheaves;
finite composition of blowups and distinguished composite ideals;
Stacks strict-transform transitivity and flat pullback;
finite product common refinements;
regular-flag etale local normal form;
Hironaka normal-flatness transitivity.
```

Each input still needs the exact scheme, marked-state, source, owner, boundary,
and Lean interface used by this project.

## Candidate boundary

The phrase `canonical homogenized packet` means the total-degree module `G[z]`
constructed from the canonical graded module `G`; it does not mean an arbitrary
projective compactification or a presentation-dependent homogenization.

The phrase `centre-exact word ideal` means the distinguished ideal constructed
from the actual word together with its centre-support certificate.  It does not
mean any ideal whose blowup happens to be isomorphic to the composite
modification.

## Forbidden extrapolations

The X041 source does not license any claim that:

```text
the relative homogenized Proj theorem has been Lean-proved;
Rydh flatifier centres are regular in positive characteristic;
the lower-dimensional strengthened principalization theorem is proved;
the common product itself is a permissible centre;
Regular-Flag Flat-Lift is proved;
overlap, smooth-base-change, or source-ledger naturality is proved;
all-chart no-reset, termination, globalization, or general resolution is proved.
```

## Truth boundary

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```
