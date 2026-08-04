# X038 Semantic Alignment

## Scope rule

The X038 Lean declarations certify only elementary module algebra, abstract
factorization, direct-sum flatness, and rank arithmetic. They do not certify
any scheme-level blowup, controlled-transform filtration, flatification,
regular-flag lift, hereditary reentry, termination, or resolution theorem.

## Candidate correction history

```text
X037 direct bifiltered interchange map
  -> rejected as too coarse;

initial X038 two-epimorphism common cospan
  -> false for J=(q*y), Sat_q(J)=(y);

final X038 primitive
  -> Old --alpha>> gr_J --beta-> gr_L,
     with ker(alpha), ker(beta), coker(beta).
```

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Exact certified content | Not certified |
|---|---|---|---|
| Relative `q`-power saturation | `PowerSaturation.powerSaturation` | A submodule defined by eventual `q`-power membership | Coherence, localization, or blowup semantics |
| Quotient torsion identity | `PowerSaturation.quotient_mk_mem_powerTorsion_iff` | A quotient class is power torsion iff its representative is in relative saturation | Identification with strict transform on a scheme chart |
| Saturation killed by regularity | `PowerSaturation.powerSaturation_eq_of_isSMulRegular_quotient` | `IsSMulRegular` on the quotient implies no new power saturation | Flat-kill theorem for coherent sheaves |
| Regular exceptional parameter has no power torsion | `PowerSaturation.powerTorsion_eq_bot_of_isSMulRegular` | Abstract module-theoretic torsion vanishing | Exceptional divisor regularity in a blowup chart |
| Controlled-core transform compiler | `ControlledCoreInterchange.Factorization.interchangeEquiv` | A surjective old-to-core map with zero kernel and a core-to-new map with zero kernel/full range yield a canonical equivalence | Construction of `alpha`, `beta`, Tor formula, Valabrega formulas, twists, charts, or overlaps |
| Bigraded packet flatness | `BigradedFlatnessCompiler.directSumFlat_iff_pieceFlat` | Flatness of the total direct sum is equivalent to flatness of all bidegrees | Finite generation of a geometric mixed-Rees module or existence of a flatifier |
| Finite portfolio compiler | `BigradedFlatnessCompiler.portfolioFlat` | Pointwise flatness of all owners and bidegrees implies flatness of the finite portfolio | Identification with the passive owner portfolio on an affine normal cone |
| Dimension-strict rank arithmetic | `FlatKillLegalizationRank.dimension_drop` and related theorems | Lexicographic drops are strict and the relation is well founded | Every actual legalization macro lowers a coordinate |

## Standard mathematical inputs identified but not Lean-closed here

```text
gr_I(A) finite type over A/I and gr_I(M) finite over it;
two-ideal mixed-Rees algebra finite type and module finite;
Noetherian homogeneous colon chains stabilize;
general U-admissible affine flatification of a finitely presented module;
regular-flag etale local normal form;
flat generically-zero finite-presentation module vanishes componentwise.
```

These inputs still require the exact scheme interfaces and edge theorems used
by this project.

## Forbidden extrapolations

The following statements are not licensed by the X038 source:

```text
scheme-level alpha and beta exist with the proposed formulas;
all transform defects are coherent and glue;
an arbitrary flatifier factors through a regular centre-enriched word;
all preparatory centres are jointly legal;
the Regular-Flag Legal-Lift Theorem is proved;
flat-kill commutes with ambient normal grading;
Cartier source compression is hereditary;
termination or globalization is proved;
general positive-characteristic resolution is proved.
```

## Candidate-manuscript labels

Every X038 manuscript theorem must carry one of:

```text
STANDARD INPUT
PROVED AFFINE ALGEBRA
LEAN-VERIFIED ABSTRACT LEAF
CANDIDATE SCHEME THEOREM
OPEN LOAD-BEARING BRIDGE
REJECTED BY COUNTEREXAMPLE.
```

The two-epimorphism cospan is `REJECTED BY COUNTEREXAMPLE`. The modal decisive
theorem is `CANDIDATE SCHEME THEOREM / OPEN LOAD-BEARING BRIDGE`.

## Formal truth

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```
