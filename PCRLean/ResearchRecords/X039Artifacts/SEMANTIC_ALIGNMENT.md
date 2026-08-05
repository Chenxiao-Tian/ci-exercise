# X039 Semantic Alignment

## Scope firewall

The X039 Lean declarations certify abstract module algebra and rank arithmetic.
They do not certify a sheafified Hironaka theorem, an actual blowup chart, a
flatifier, a regular trace word, hereditary reentry, termination, or resolution.

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Exact certified content | Not certified |
|---|---|---|---|
| Hironaka tensor-flatness endpoint | `HironakaTensorFlatnessCompiler.Certificate.totalFlat` | A supplied linear equivalence from a tensor of two flat modules transports flatness to the target | Existence/naturality of Hironaka's comparison for schemes |
| Flatness equivalence | `HironakaTensorFlatnessCompiler.Certificate.flat_iff_tensorFlat` | Flatness is invariant under the supplied linear equivalence | Complete-intersection hypotheses or conormal geometry |
| Finite owner compiler | `HironakaTensorFlatnessCompiler.PortfolioCertificate.portfolioFlat` | Ownerwise abstract comparisons and flat factors imply flatness of the direct-sum portfolio | Identification with passive owners on a carrier |
| Exceptional no recharge | `ExceptionalNoRecharge.noRecharge` | A flat module has no submodule elementwise killed by powers of a supplied base nonzerodivisor | Construction of an SNC exceptional monomial on a scheme chart |
| Successor no recharge | `ExceptionalNoRecharge.successor_eq_bot` | Any successor submodule with the same monomial-torsion property is zero | Unique source transport or chart overlap |
| Carrier-dimension rank | `NestedCarrierLegalizationRank.carrier_dimension_drop` | A smaller first coordinate is lexicographically strict | Every recursive geometric call uses a proper subcarrier |
| Word-height rank | `NestedCarrierLegalizationRank.word_height_drop` | A smaller immutable word height is strict | Existence and immutability of a flatifier-realization word |
| Rank well-foundedness | `NestedCarrierLegalizationRank.rank_wellFounded` | The five-coordinate lexicographic order is well founded | Coverage of all geometric successors by a strict branch |

## Standard mathematical input

The module form of Hironaka's normal-flatness theorem supplies, under its exact
complete-intersection and freeness hypotheses, a graded comparison of the form

```text
(gr_I(M)/J gr_I(M)) tensor_(R/J) gr_(J/I)(R/I) ~= gr_J(M).
```

X039 uses this only as a standard input candidate.  The project still needs its
exact sheafified finite-owner formulation, base-change law, and connection to
the carrier state.

## Candidate geometric theorem

The following remains unverified:

```text
D subset C subset X jointly legal regular flag
-> on every relevant blowup chart
   gr_(C')(M')
   ~= ST_D(gr_C(M)) tensor exceptional grading twist
-> overlap and smooth-base-change compatibility
-> flatness persists and purification torsion vanishes
-> all source/debt/boundary identities reenter without reset.
```

It may not be cited as a proved theorem merely because the coordinate ideal
normal form and abstract flatness endpoints are available.

## Forbidden extrapolations

The X039 source does not license any of the following:

```text
normal flatness is transitive for arbitrary nested closed subschemes;
regularity alone implies passive safety;
a general flatifier has regular centres;
a bare morphism dominating a flatifier preserves strict transforms;
only one blowup chart needs checking;
exceptional torsion cannot reappear without a source/Cartier certificate;
the universal jointly legal centre word exists;
local or global termination is proved;
general positive-characteristic resolution is proved.
```

## Manuscript labels

Every statement in an X039 candidate manuscript must be marked as one of:

```text
STANDARD PRIMARY-SOURCE INPUT
PROVED ABSTRACT ALGEBRA
LEAN-VERIFIED EXPERIMENTAL LEAF
CANDIDATE SCHEME THEOREM
OPEN LOAD-BEARING EDGE
REJECTED OR RESTRICTED BY COUNTEREXAMPLE.
```

## Formal truth

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```
