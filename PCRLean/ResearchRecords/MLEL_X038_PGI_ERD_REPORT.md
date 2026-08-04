# MLEL-X038 / PGI-ERD

## Purification–Grading Interchange, Exceptional Rees Defects, and Divisorial Descent

**Chinese title:** 纯化–分次交换、例外 Rees 缺陷与除子下降  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted formal parent:** `MLEL-M004 / HMC-SCCD` in its restricted scope  
**Experimental parents:** `MLEL-X036 / PNF-ACL`, `MLEL-X037 / CTW-BRT`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

## 1. Central local theorem

Let `R` be Noetherian, `L` an ideal, `N` a finite module, and `u` a local equation of one exceptional Cartier component. Put

```text
T = H^0_(u)(N),
A = gr_L(N),
H = gr_L^ind(T),
U = H^0_(u)(A).
```

The induced filtration on `T` and quotient filtration on `N/T` give

```text
0 -> H -> A -> gr_L(N/T) -> 0.
```

Noetherian stabilization supplies one exponent killing `T`, hence `H <= U`. Therefore

```text
0 -> U/H -> gr_L(N/T) -> A/U -> 0.
```

Moreover

```text
U/H = H^0_(u)(gr_L(N/T)).
```

Thus purification before and after associated grading differ by one finite exceptional graded-torsion kernel. The defect is not an arbitrary full-dimensional kernel/cokernel.

In degree `a`, the defect is

```text
(((L^(a+1)N : u^infinity) intersection L^aN)
 /
 (L^(a+1)N + (T intersection L^aN))).
```

The associated graded ring is Noetherian and `A` is finite, so `H`, `U`, and `U/H` are finite graded modules. Artin–Rees gives a finite transition window and eventual tail. Flat base change preserves the stabilized exceptional torsion, powers, intersections, quotient filtrations, and hence the exact packet.

## 2. Sharp example

Let

```text
R = k[u,x],
N = R,
L = (u*x, x^2).
```

The original module is `u`-torsion-free. In degree zero of `gr_L(N)`, however, the nonzero class of `x` is killed by `u`. Thus associated grading can create new exceptional torsion even when the ambient module has none. The purification–grading packet is therefore indispensable.

## 3. Two-stage total interchange defect

X037 also requires a twisted chartwise Rees comparison between the old projective-normal packet and the associated graded of the ambient pullback. Once constructed, its coherent kernel and cokernel are supported on the exceptional divisor because the comparison is an isomorphism off that divisor.

The total Rees interchange defect should therefore have a finite filtration with two types of subquotient:

```text
B = twisted Rees base-change / line-twist defect,
E = purification–grading torsion U/H.
```

Both are finite exceptional-supported packets. Vanishing gives exact ambient/projective-normal transport. Nonvanishing creates a lower-dimensional exceptional task.

## 4. Defect-elimination macro

```text
construct B and E
-> fuse finite Fitting/projective-tail packets
-> zero: accept transform comparison
-> nonzero: support lies in exceptional boundary
-> lower-dimensional relative flatification/principalization
-> ambient source-labelled Cartier-trace lift
-> strict drop in support dimension, exceptional exponent,
   or projective-tail/Fitting profile
-> reconstruct all charts and overlaps without reset.
```

The proposed rank begins with

```text
(dim support of total interchange defect,
 exceptional torsion / Artin–Rees exponent,
 projective-tail/Fitting profile,
 passive complexity,
 contact,
 debt,
 SCC height).
```

## 5. Candidate-graph update

The X037 edge

```text
arbitrary RID kernel/cokernel -> strict recursion
```

is replaced by

```text
ambient trace chart
-> twisted Rees base-change packet B

ambient exceptional purification
-> inherited torsion H <= full graded torsion U
-> exact packet E=U/H

B plus E
-> finite exceptional interchange packet
-> zero chamber: exact projective-normal transport
-> nonzero chamber: divisorial lower-dimensional legalization
-> source-labelled Cartier-trace lift
-> no-reset comparison reentry.
```

This serves the D001 critical path

```text
HER-03 -> HER-05 -> HER-15 -> TRM-05 -> TRM-11 -> TRM-12.
```

## 6. Lean slice

```text
ExceptionalTorsionLayers.lean
ArtinReesTailCompiler.lean
ExceptionalInterchangeRank.lean
X038PurificationGradingInterchangeIndex.lean
X038PurificationGradingInterchangeIndexAudit.lean
```

The exact slice proves nested-layer clean/defect coverage, witness existence, finite-prefix/tail induction, and the well-founded support/exponent/tail/passive/contact/debt arithmetic. It does not formalize the scheme-level exact sequence, Artin–Rees, base change, chartwise Rees comparison, defect elimination, or no-reset.

## 7. Exact frontier

```text
X038-G1   SHEAFIFIED_EXCEPTIONAL_TORSION_FUNCTOR
X038-G2   INDUCED_FILTRATION_ASSOCIATED_GRADED_EXACT_SEQUENCE
X038-G3   PURIFICATION_GRADING_TORSION_IDENTITY
X038-G4   FINITE_GRADED_PACKET_AND_ARTIN_REES_WINDOW
X038-G5   FLAT_BASE_CHANGE_OF_EXCEPTIONAL_TORSION_AND_INTERSECTIONS
X038-G6   MULTI_EXCEPTIONAL_MONOMIAL_TORSION_PACKET
X038-G7   ALL_CHART_TWISTED_REES_BASE_CHANGE_MAP
X038-G8   NORMAL_BUNDLE_LINE_TWIST_IDENTIFICATION
X038-G9   FINITE_REES_BASE_CHANGE_DEFECT
X038-G10  TOTAL_INTERCHANGE_DEFECT_FILTRATION
X038-G11  EXCEPTIONAL_SUPPORT_AND_LOWER_DIMENSIONAL_CARRIER
X038-G12  DEFECT_FLATIFICATION_AND_AMBIENT_CARTIER_TRACE_LIFT
X038-G13  STRICT_SUPPORT_EXPONENT_OR_TAIL_DROP
X038-G14  SOURCE_LABEL_AND_ZERO_DEFECT_NO_RECHARGE
X038-G15  OVERLAP_COCYCLE_FOR_THE_COMPARISON
X038-G16  PROJECTIVE_NORMAL_FLATNESS_AFTER_DEFECT_ELIMINATION
X038-G17  WONDERFUL_WORD_COMPATIBILITY
X038-G18  ALL_CHART_PACKET_RECONSTRUCTION_WITHOUT_RESET
X038-G19  COMPOSITE_DIMENSION_DEFECT_EXPONENT_TAIL_DEBT_SCC_RANK
X038-G20  UNIVERSAL_JOINTLY_LEGAL_ACTUAL_CENTRE_WORD
```

Highest-information cut:

```text
G7/G8/G9 + G12/G13 + G14/G18.
```

## 8. Annals maximum-likelihood plan

The central estimate is six papers and 564 dense Annals/AMS-equivalent pages:

```text
I    Intrinsic Frobenius–Hasse States, Affine Conormal Packets,
     and Projectivity Discriminants                              90
II   Anchor-Contact Ideals, Cartier-Trace Words,
     and Wonderful Actual-Centre Synthesis                     118
III  Purification–Grading Interchange, Carrier-Enriched
     Flatification, and Hereditary Reentry                     142
IV   Exceptional Rees Defects, Source–Debt Causality,
     and Termination                                            88
V    Global Descent, Symmetry-Compatible Serialization,
     and Principalization                                      78
VI   Functorial Resolution, Counterexample Closure,
     and Lean Reproducibility                                  48
                                                               ---
                                                               564
```

A single-volume editorial edition is estimated at 612–652 physical pages.

## 9. Truth boundary

```text
PURIFICATION_GRADING_EXACT_SEQUENCE_PROVED_ON_PAPER = true
NEW_TORSION_IDENTITY_PROVED_ON_PAPER                = true
FINITE_GRADED_DEFECT_PROVED_ON_PAPER                = true
FLAT_BASE_CHANGE_PROVED_ON_PAPER                    = true
X038_EXPERIMENTAL_CLEANROOM_GREEN                   = true
ALL_CHART_TWISTED_REES_MAP_PROVED                   = false
DEFECT_ELIMINATION_STRICT_DROP_PROVED               = false
ZERO_DEFECT_NO_RECHARGE_PROVED                      = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED          = false
NEW_DECLARATIONS_PROMOTED                           = false
CERTIFIED_GRAPH_CHANGED                             = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                  = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION          = false
FORMAL_GLOBAL_STATUS                                = OPEN_GAP
```
