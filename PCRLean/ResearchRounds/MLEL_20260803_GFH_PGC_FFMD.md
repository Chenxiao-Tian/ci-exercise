# MLEL Experimental Research Record — 2026-08-03

## Graded Frobenius Heredity, Polynomial-Graph Centres, Exceptional Debt, and Faithfully Flat Marked Descent

**Protocol:** PCR-JUMP-LEAN 2.0  
**Official accepted node:** MLEL-M004 / HMC-SCCD  
**Certified Graph changed:** no  
**General positive-characteristic resolution proved:** no  
**Global status:** `OPEN_GAP`

## Purpose of this baseline record

This file registers the complete current experimental frontier without importing any experimental theorem into the certified dependency graph. Full reports, the conversation-output audit, progress-ledger supplement, machine state, GitHub live snapshot and hashes are stored in the persistent MLE–Lean library under:

```text
/正特征奇点消解/MLE-Lean线/ResearchRounds/
  2026-08-03_GFH_PGC_FFMD/
```

## Mathematical progress recorded

### Graded Frobenius heredity

Bare integral equivalence was rejected as too weak. Frobenius-root normalization must preserve the marked grading. The current experimental law is

```text
x^(p^e) ∈ I^m
  ↔
x ∈ I^(ceil(m / p^e))
```

under the graded-power/normal-cone nonvanishing interface.

### Polynomial graph centres

For a graph centre

```text
I_h = (Z_i - h_i)
```

in a polynomial ring over a Noetherian regular domain, experimental modules now package:

- an actual ideal;
- non-top and non-bottom strictness;
- finite generation;
- exact quotient by the coefficient ring;
- regular quotient;
- Frobenius-normality;
- marked permissibility;
- every standard blowup chart.

### Pure exceptional-debt classification

For `q = p^e` and `0 < mark ≤ q`, every graph chart has exact controlled residual ideal

```text
(exceptional pivot)^(q - mark).
```

Hence `mark = q` is terminal, while `mark < q` leaves only a positive bounded exceptional debt. No hidden nonmonomial residual equation remains in this chamber.

### Faithfully flat marked-centre descent

The newest experimental module is

```text
PCRLean.Experimental.FaithfullyFlatMarkedCentreDescent
```

It attempts to prove, without new axioms, that faithful-flat extension reflects ideal containment and equality, and therefore descends:

- centre uniqueness;
- marked permissibility;
- non-top/non-bottom strictness;
- finite type over a Noetherian base;
- Frobenius-normality from an exact graph model.

This is the algebraic core of the proposed adapted étale/fpqc graph-atlas bridge.

## Current experimental source

```text
branch:
  pcr-jump-integral-heredity-20260803

integrated index:
  PCRLean.Experimental.GradedFrobeniusHeredityKernelIndex

new bridge:
  PCRLean.Experimental.FaithfullyFlatMarkedCentreDescent
```

Exact CI status must be read from the attached live snapshot or GitHub Actions. Source text alone is not classified as kernel green.

## Highest-priority unresolved bridges

1. finite adapted étale/fpqc graph atlas for every actual regular candidate centre;
2. blowup and controlled-transform descent through that atlas;
3. passive Tor/normal-flatness and boundary SNC for the same centre;
4. global cocycle/no-recharge identity for the debt `p^e - mark`;
5. hereditary reconstruction of packets, owners and histories on every chart;
6. canonical packet-to-graph/hybrid centre or strict escape;
7. rank-zero nonlinear/radicial and immediate-defect exits;
8. finite global serialization and the final resolution compiler.

## Permanent truth boundary

```text
EXPERIMENTAL_RESULTS_PROMOTED = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS = OPEN_GAP
```
