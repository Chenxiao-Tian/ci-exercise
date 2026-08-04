# X038 Semantic Alignment

## Scope rule

The X038 Lean declarations certify only elementary module algebra and rank
arithmetic.  They do not certify any scheme-level blowup, flatification,
common-core sheaf, or resolution theorem.

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Exact certified content | Not certified |
|---|---|---|---|
| Relative `q`-power saturation | `PowerSaturation.powerSaturation` | A submodule defined by eventual `q`-power membership | Coherence, localization, or blowup semantics |
| Quotient torsion identity | `PowerSaturation.quotient_mk_mem_powerTorsion_iff` | A quotient class is power torsion iff its representative is in relative saturation | Identification with strict transform on a scheme chart |
| Saturation killed by regularity | `PowerSaturation.powerSaturation_eq_of_isSMulRegular_quotient` | `IsSMulRegular` on the quotient implies no new power saturation | Flat-kill theorem for coherent sheaves |
| Common-core equivalence | `CommonCoreInterchange.Cospan.interchangeEquiv` | Two surjective linear maps with zero kernels give an equivalence | Construction of geometric left/right maps or kernel formulas |
| Compatibility through the core | `CommonCoreInterchange.Cospan.rightMap_interchangeEquiv_apply` | The induced equivalence commutes with the two abstract maps | Overlap/base-change compatibility of geometric charts |
| Dimension-strict rank arithmetic | `FlatKillLegalizationRank.dimension_drop` and related theorems | Lexicographic drops are strict and the relation is well founded | Every actual legalization macro lowers a coordinate |

## Forbidden extrapolations

The following statements are not licensed by the X038 source:

```text
all Tor-Valabrega kernels are coherent;
all degrees are controlled by one finite packet;
a regular word realizing every flatifier exists;
all preparatory centres are jointly legal;
flat-kill commutes with ambient normal grading;
hereditary reentry is proved;
termination is proved;
general positive-characteristic resolution is proved.
```

## Candidate-manuscript labels

Every X038 manuscript theorem must carry one of:

```text
STANDARD INPUT
PROVED AFFINE ALGEBRA
LEAN-VERIFIED ABSTRACT LEAF
CANDIDATE SCHEME THEOREM
OPEN LOAD-BEARING BRIDGE.
```

The modal decisive theorem is currently `CANDIDATE SCHEME THEOREM / OPEN
LOAD-BEARING BRIDGE`.

## Formal truth

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```
